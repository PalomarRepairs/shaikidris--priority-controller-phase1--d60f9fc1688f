module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Mathlib.Data.List.FinRange
public import Controller.Cost.ForestZeroGrammar
public import Controller.Cost.ForestZeroRootLoop
public import Controller.Cost.ForestZeroReset
public import Controller.Cost.ForestZeroCallerWiden
public import Controller.Cost.ForestZeroAdmissible
public import Controller.Cost.ForestZeroQueryCaller
public import Controller.Horn.NormalizeInitialize
public import Controller.Cost.ForestZeroIndexMarks
public import Controller.Cost.ForestZeroNormalizeFrame

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! The optional nonemptiness row uses a reserved empty directory entry.
The fixed caller reads both actual endpoints before searching, preserves the
allocator count on the stack, and dispatches from the executed search PC.
The unused branch excludes the reserved row; the covered branch fills it.
-/
namespace Controller.Cost.ForestZeroAdmissibleCaller
open Controller.CNF Controller.Cost.GateProgram Controller.Cost.ForestZeroTouch
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroAdmissible Controller.Cost.ForestZeroEmit
open Controller.Horn.SourceDirectory Controller.Horn.SourceScan Controller.Horn.RowScan

/-- Two actual query-header loads retain the source and reserved directory
endpoints below the saved local count. -/
def saveEndpointsCode (width recordHeader endHeader : ℕ) : Code width :=
  [.constant 0 (word width recordHeader), .load 0 0, .push 0,
   .constant 0 (word width endHeader), .load 0 0, .push 0]

/-- A fixed trampoline performs an actual branch without a semantic result
oracle. Search exits land on separate covered and unused trampolines. -/
def jumpCode (width target : ℕ) : Code width :=
  [.constant 3 (word width 0), .branchZero 3 (word width target)]

/-- Restore saved endpoints and retain count while computing the appended
source endpoint from the actual channel header and reserved directory slot. -/
def coveredPrepareCode (width : ℕ) : Code width :=
  [.pop 2, .pop 3, .pop 0, .push 2,
   .constant 1 (word width 0), .load 1 1, .add 1 1 1, .add 1 0 1,
   .constant 2 (word width (2 ^ width - 1)), .add 3 3 2, .add 3 3 2]

/-- Activate the original rows only, excluding the untouched reserved empty
row. The count is recovered by a physical pop before header activation. -/
def unusedPrepareCode (width : ℕ) : Code width :=
  [.pop 2, .pop 3, .pop 0, .constant 1 (word width (2 ^ width - 1)),
   .add 3 3 1, .add 3 3 1, .copy 1 0, .copy 0 3]

/-- The covered branch appends exactly one channel clause then installs its
source endpoints and recovers the saved local count for the hot backend. -/
def coveredCode (width base recordHeader endHeader returnPC : ℕ) : Code width :=
  ForestZeroPositive.fullCode width base ++ coveredPrepareCode width ++ boundaryCode width ++
    [.add 3 3 2, .copy 0 3] ++ activeCode width recordHeader endHeader ++ [.pop 2] ++
    jumpCode width returnPC

def unusedCode (width recordHeader endHeader returnPC : ℕ) : Code width :=
  unusedPrepareCode width ++ activeCode width recordHeader endHeader ++ jumpCode width returnPC

/-- Fixed code has two actual search-exit trampolines and one shared return. -/
def code (width base recordHeader endHeader returnPC : ℕ) : Code width :=
  saveEndpointsCode width recordHeader endHeader ++ savedSearchCode width (base + 6) ++
    jumpCode width (base + 29) ++ jumpCode width (base + 67) ++
    coveredCode width (base + 29) recordHeader endHeader returnPC ++
    unusedCode width recordHeader endHeader returnPC

@[simp] theorem saveEndpointsCode_length : (saveEndpointsCode width recordHeader endHeader).length = 6 := rfl
@[simp] theorem jumpCode_length : (jumpCode width target).length = 2 := rfl
@[simp] theorem coveredPrepareCode_length : (coveredPrepareCode width).length = 11 := rfl
@[simp] theorem unusedPrepareCode_length : (unusedPrepareCode width).length = 8 := rfl
@[simp] theorem coveredCode_length : (coveredCode width base recordHeader endHeader returnPC).length = 38 := by
  simp only [coveredCode, List.length_append, ForestZeroPositive.fullCode_length,
    coveredPrepareCode_length, boundaryCode_length, activeCode_length, jumpCode_length,
    List.length_cons, List.length_nil]
@[simp] theorem unusedCode_length : (unusedCode width recordHeader endHeader returnPC).length = 14 := by
  simp only [unusedCode, List.length_append, unusedPrepareCode_length, activeCode_length, jumpCode_length]
@[simp] theorem code_length : (code width base recordHeader endHeader returnPC).length = 81 := by
  simp only [code, List.length_append, saveEndpointsCode_length, savedSearchCode_length,
    jumpCode_length, coveredCode_length, unusedCode_length]

private theorem fetched (program : Program width 4) (state : State width 4)
    (cursor : ℕ) (instruction : Instruction width 4)
    (pc : state.pc = word width cursor) (fits : cursor < 2 ^ width)
    (entry : program[cursor]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [pc, show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits, entry]
  rfl

private theorem advance_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 : ℕ)
    (stack output : List (Word width)) (fits : cursor < 2 ^ width) :
    (atState heap cursor x0 x1 x2 x3 stack output).advance =
      atState heap (cursor + 1) x0 x1 x2 x3 stack output := by
  simp [atState, State.advance, show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits]

private theorem put0_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 0 (word width value) =
      atState heap cursor value x1 x2 x3 stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

private theorem put3_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 3 (word width value) =
      atState heap cursor x0 x1 x2 value stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

/-- The jump preserves physical source, caller stack and allocator registers. -/
theorem jump_execution (program : Program width 4) (heap : Array (Word width))
    (base target x0 x1 x2 scratch : ℕ) (stack output : List (Word width))
    (fits : base + 2 < 2 ^ width) (block : BlockAt program base (jumpCode width target)) :
    Execution program (atState heap base x0 x1 x2 scratch stack output)
      (atState heap target x0 x1 x2 0 stack output) 2
      (5 + heap.size + stack.length + output.length) := by
  let s0 := atState heap base x0 x1 x2 scratch stack output
  let s1 := atState heap (base + 1) x0 x1 x2 0 stack output
  let s2 := atState heap target x0 x1 x2 0 stack output
  have t0 : programStep program s0 = some s1 := by
    rw [fetched program s0 base (.constant 3 (word width 0)) rfl (by omega)
      (by simpa [jumpCode] using block 0 (by simp [jumpCode]))]
    change some (s0.advance.put 3 (word width 0)) = some s1
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.branchZero 3 (word width target)) rfl (by omega)
      (by simpa [jumpCode] using block 1 (by simp [jumpCode]))]
    change some (if (word width 0).val = 0 then { s1.advance with pc := word width target } else s1.advance) = some s2
    simp only [word, Nat.zero_mod, ite_true, s1, s2, atState, State.advance]
  convert Execution.cons t0 (Execution.cons t1 (Execution.refl s2)) using 1 <;>
    simp only [s0, s1, s2, atState, State.liveWords, Nat.max_self] <;> omega

/-- Three fetched header operations save one actual endpoint. -/
theorem save_endpoint_execution (program : Program width 4) (heap : Array (Word width))
    (base header value x0 x1 x2 x3 : ℕ) (stack output : List (Word width))
    (valid : header < heap.size) (headerFits : header < 2 ^ width)
    (cell : heap[header]? = some (word width value)) (fits : base + 3 < 2 ^ width)
    (block : BlockAt program base [.constant 0 (word width header), .load 0 0, .push 0]) :
    Execution program (atState heap base x0 x1 x2 x3 stack output)
      (atState heap (base + 3) value x1 x2 x3 (word width value :: stack) output)
      3 (6 + heap.size + stack.length + output.length) := by
  let s0 := atState heap base x0 x1 x2 x3 stack output
  let s1 := atState heap (base + 1) header x1 x2 x3 stack output
  let s2 := atState heap (base + 2) value x1 x2 x3 stack output
  let s3 := atState heap (base + 3) value x1 x2 x3 (word width value :: stack) output
  have actual : heap[header] = word width value := by
    rw [Array.getElem?_eq_getElem valid] at cell
    exact Option.some.inj cell
  have t0 : programStep program s0 = some s1 := by
    rw [fetched program s0 base (.constant 0 (word width header)) rfl (by omega)
      (by simpa using block 0 (by simp))]
    change some (s0.advance.put 0 (word width header)) = some s1
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.load 0 0) rfl (by omega)
      (by simpa using block 1 (by simp))]
    change (if h : (word width header).val < heap.size then
      some (s1.advance.put 0 heap[(word width header).val]) else none) = some s2
    rw [show (word width header).val = header from Nat.mod_eq_of_lt headerFits,
      dite_eq_left valid, actual, advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (base + 2) (.push 0) rfl (by omega)
      (by simpa using block 2 (by simp))]
    change some { s2.advance with stack := word width value :: stack } = some s3
    rw [advance_at _ _ _ _ _ _ _ _ (by omega)]
    rfl
  convert Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl s3))) using 1 <;>
    simp only [s0, s1, s2, s3, atState, State.liveWords, List.length_cons] <;> omega

/-- Both retained endpoint words come from actual query-header reads. -/
theorem save_endpoints_execution (program : Program width 4) (heap : Array (Word width))
    (base recordHeader endHeader sourceEnd directoryEnd x0 table count scratch : ℕ)
    (stack output : List (Word width))
    (recordValid : recordHeader < heap.size) (endValid : endHeader < heap.size)
    (recordFits : recordHeader < 2 ^ width) (endFits : endHeader < 2 ^ width)
    (sourceCell : heap[recordHeader]? = some (word width sourceEnd))
    (directoryCell : heap[endHeader]? = some (word width directoryEnd))
    (fits : base + 6 < 2 ^ width)
    (block : BlockAt program base (saveEndpointsCode width recordHeader endHeader)) :
    Execution program (atState heap base x0 table count scratch stack output)
      (atState heap (base + 6) directoryEnd table count scratch
        (word width directoryEnd :: word width sourceEnd :: stack) output)
      6 (7 + heap.size + stack.length + output.length) := by
  let firstCode : Code width := [.constant 0 (word width recordHeader), .load 0 0, .push 0]
  let lastCode : Code width := [.constant 0 (word width endHeader), .load 0 0, .push 0]
  have whole : BlockAt program base (firstCode ++ lastCode) := block
  have first := save_endpoint_execution program heap base recordHeader sourceEnd x0 table count scratch
    stack output recordValid recordFits sourceCell (by omega) (BlockAt.prefix program base _ _ whole)
  have tail : BlockAt program (base + 3) lastCode := by
    simpa only [firstCode, List.length_cons, List.length_nil] using BlockAt.suffix program base firstCode lastCode whole
  have last := save_endpoint_execution program heap (base + 3) endHeader directoryEnd sourceEnd table count scratch
    (word width sourceEnd :: stack) output endValid endFits directoryCell (by omega) tail
  convert first.append last using 1 <;>
    simp only [List.length_cons, Nat.add_assoc] <;> omega

/-- Actual search PCs select the two fixed trampolines. The result is a ghost
index of the executed trace, never a supplied branch instruction. -/
theorem search_dispatch_execution (program : Program width 4) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient)
    (represented : Represented heap layout state)
    (base recordHeader endHeader sourceEnd directoryEnd channels input scratch : ℕ)
    (stack output : List (Word width))
    (within : channels ≤ ambient) (valid : 0 < heap.size)
    (channelCell : heap[0]? = some (word width channels))
    (recordValid : recordHeader < heap.size) (endValid : endHeader < heap.size)
    (recordFits : recordHeader < 2 ^ width) (endFits : endHeader < 2 ^ width)
    (sourceCell : heap[recordHeader]? = some (word width sourceEnd))
    (directoryCell : heap[endHeader]? = some (word width directoryEnd))
    (heapFits : heap.size < 2 ^ width) (ambientFits : ambient + 1 < 2 ^ width)
    (fits : base + 81 < 2 ^ width)
    (block : BlockAt program base (code width base recordHeader endHeader returnPC)) :
    let result := ForestZeroNonempty.search state (state.coordinates.size + 1) channels 0
    ∃ ticks, Execution program (atState heap base input layout.tableBase state.coordinates.size scratch stack output)
      (atState heap (if result.reason = .covered then base + 29 else base + 67)
        (channels - result.marked) (state.coordinates.size + 1 - result.marked)
        (layout.tableBase + result.marked) 0
        (word width state.coordinates.size :: word width directoryEnd :: word width sourceEnd :: stack) output)
      ticks (8 + heap.size + stack.length + output.length) ∧
      ticks ≤ 11 * min channels (state.coordinates.size + 1) + 20 ∧
      result.reason ≠ .exhausted := by
  let endpoints := saveEndpointsCode width recordHeader endHeader
  let searchCode := savedSearchCode width (base + 6)
  let coveredJump := jumpCode width (base + 29)
  let unusedJump := jumpCode width (base + 67)
  let covered := coveredCode width (base + 29) recordHeader endHeader returnPC
  let unused := unusedCode width recordHeader endHeader returnPC
  have whole : BlockAt program base (endpoints ++ (searchCode ++ (coveredJump ++ (unusedJump ++ (covered ++ unused))))) := block
  have endpointsBlock := BlockAt.prefix program base _ _ whole
  have afterEndpoints : BlockAt program (base + 6) (searchCode ++ (coveredJump ++ (unusedJump ++ (covered ++ unused)))) := by
    simpa only [endpoints, saveEndpointsCode_length] using BlockAt.suffix program base _ _ whole
  have searchBlock := BlockAt.prefix program (base + 6) _ _ afterEndpoints
  have afterSearch : BlockAt program (base + 25) (coveredJump ++ (unusedJump ++ (covered ++ unused))) := by
    simpa only [searchCode, savedSearchCode_length, Nat.add_assoc] using BlockAt.suffix program (base + 6) _ _ afterEndpoints
  have coveredBlock := BlockAt.prefix program (base + 25) _ _ afterSearch
  have afterCoveredJump : BlockAt program (base + 27) (unusedJump ++ (covered ++ unused)) := by
    simpa only [coveredJump, jumpCode_length, Nat.add_assoc] using BlockAt.suffix program (base + 25) _ _ afterSearch
  have unusedBlock := BlockAt.prefix program (base + 27) _ _ afterCoveredJump
  have first := save_endpoints_execution program heap base recordHeader endHeader sourceEnd directoryEnd input
    layout.tableBase state.coordinates.size scratch stack output recordValid endValid recordFits endFits sourceCell directoryCell (by omega) endpointsBlock
  obtain ⟨searchTicks, searchTrace, searchBound, notExhausted⟩ := saved_search_execution program heap layout state represented
    (base + 6) channels directoryEnd scratch (word width directoryEnd :: word width sourceEnd :: stack) output
    within channelCell valid heapFits ambientFits (by omega) searchBlock
  let result := ForestZeroNonempty.search state (state.coordinates.size + 1) channels 0
  have initialTrace := first.append searchTrace
  cases reasonEq : result.reason with
  | exhausted => exact False.elim (notExhausted reasonEq)
  | covered =>
    have initialTrace' : Execution program
        (atState heap base input layout.tableBase state.coordinates.size scratch stack output)
        (atState heap (base + 25) (channels - result.marked) (state.coordinates.size + 1 - result.marked)
          (layout.tableBase + result.marked) 0
          (word width state.coordinates.size :: word width directoryEnd :: word width sourceEnd :: stack) output)
        (6 + searchTicks) (8 + heap.size + stack.length + output.length) := by
      convert initialTrace using 1 <;>
        simp only [result, reasonEq, ForestZeroNonempty.exitOffset, List.length_cons, Nat.add_assoc] <;> omega
    have jump := jump_execution program heap (base + 25) (base + 29)
      (channels - result.marked) (state.coordinates.size + 1 - result.marked) (layout.tableBase + result.marked) 0
      (word width state.coordinates.size :: word width directoryEnd :: word width sourceEnd :: stack) output (by omega) coveredBlock
    refine ⟨6 + searchTicks + 2, ?_, by omega, notExhausted⟩
    convert initialTrace'.append jump using 1 <;>
      (try simp only [result, reasonEq, ite_true, List.length_cons, Nat.add_assoc, Nat.max_self]) <;> omega
  | unused =>
    have initialTrace' : Execution program
        (atState heap base input layout.tableBase state.coordinates.size scratch stack output)
        (atState heap (base + 27) (channels - result.marked) (state.coordinates.size + 1 - result.marked)
          (layout.tableBase + result.marked) 0
          (word width state.coordinates.size :: word width directoryEnd :: word width sourceEnd :: stack) output)
        (6 + searchTicks) (8 + heap.size + stack.length + output.length) := by
      convert initialTrace using 1 <;>
        simp only [result, reasonEq, ForestZeroNonempty.exitOffset, List.length_cons, Nat.add_assoc] <;> omega
    have jump := jump_execution program heap (base + 27) (base + 67)
      (channels - result.marked) (state.coordinates.size + 1 - result.marked) (layout.tableBase + result.marked) 0
      (word width state.coordinates.size :: word width directoryEnd :: word width sourceEnd :: stack) output (by omega) unusedBlock
    refine ⟨6 + searchTicks + 2, ?_, by omega, notExhausted⟩
    convert initialTrace'.append jump using 1 <;>
      (try simp only [result, reasonEq, reduceCtorEq, ite_false, List.length_cons, Nat.add_assoc, Nat.max_self]) <;> omega

private theorem put2_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 2 (word width value) =
      atState heap cursor x0 x1 value x3 stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

private theorem pop_execution (program : Program width 4) (heap : Array (Word width))
    (base x0 x1 x2 x3 value : ℕ) (register : Fin 4) (stack output : List (Word width))
    (fits : base + 1 < 2 ^ width) (entry : program[base]? = some (.pop register)) :
    Execution program (atState heap base x0 x1 x2 x3 (word width value :: stack) output)
      ((atState heap (base + 1) x0 x1 x2 x3 stack output).put register (word width value))
      1 (6 + heap.size + stack.length + output.length) := by
  let first := atState heap base x0 x1 x2 x3 (word width value :: stack) output
  let last := (atState heap (base + 1) x0 x1 x2 x3 stack output).put register (word width value)
  have transition : programStep program first = some last := by
    rw [fetched program first base (.pop register) rfl (by omega) entry]
    change some (({ first.advance with stack := stack }).put register (word width value)) = some last
    rw [advance_at _ _ _ _ _ _ _ _ (by omega)]
    rfl
  convert Execution.cons transition (Execution.refl last) using 1 <;>
    simp only [first, last, atState, State.put, State.liveWords, List.length_cons] <;> omega

private theorem push2_execution (program : Program width 4) (heap : Array (Word width))
    (base x0 x1 count x3 : ℕ) (stack output : List (Word width))
    (fits : base + 1 < 2 ^ width) (entry : program[base]? = some (.push 2)) :
    Execution program (atState heap base x0 x1 count x3 stack output)
      (atState heap (base + 1) x0 x1 count x3 (word width count :: stack) output)
      1 (6 + heap.size + stack.length + output.length) := by
  let first := atState heap base x0 x1 count x3 stack output
  let last := atState heap (base + 1) x0 x1 count x3 (word width count :: stack) output
  have transition : programStep program first = some last := by
    rw [fetched program first base (.push 2) rfl (by omega) entry]
    change some { first.advance with stack := word width count :: stack } = some last
    rw [advance_at _ _ _ _ _ _ _ _ (by omega)]
    rfl
  convert Execution.cons transition (Execution.refl last) using 1 <;>
    simp only [first, last, atState, State.liveWords, List.length_cons] <;> omega

/-- Endpoint recovery uses three real pops. The count is physically restored
before any backend entry, and no mutable header is used as a count oracle. -/
theorem restore_endpoints_execution (program : Program width 4) (heap : Array (Word width))
    (base x0 x1 x2 x3 count directoryEnd sourceEnd : ℕ) (stack output : List (Word width))
    (fits : base + 3 < 2 ^ width) (block : BlockAt program base [.pop 2, .pop 3, .pop 0]) :
    Execution program
      (atState heap base x0 x1 x2 x3
        (word width count :: word width directoryEnd :: word width sourceEnd :: stack) output)
      (atState heap (base + 3) sourceEnd x1 count directoryEnd stack output)
      3 (8 + heap.size + stack.length + output.length) := by
  have t0 : Execution program
      (atState heap base x0 x1 x2 x3
        (word width count :: word width directoryEnd :: word width sourceEnd :: stack) output)
      (atState heap (base + 1) x0 x1 count x3 (word width directoryEnd :: word width sourceEnd :: stack) output)
      1 (8 + heap.size + stack.length + output.length) := by
    convert pop_execution program heap base x0 x1 x2 x3 count 2
        (word width directoryEnd :: word width sourceEnd :: stack) output (by omega)
        (by simpa using block 0 (by simp)) using 1 <;>
      simp only [put2_at, List.length_cons, Nat.add_assoc] <;> omega
  have t1 : Execution program
      (atState heap (base + 1) x0 x1 count x3 (word width directoryEnd :: word width sourceEnd :: stack) output)
      (atState heap (base + 2) x0 x1 count directoryEnd (word width sourceEnd :: stack) output)
      1 (7 + heap.size + stack.length + output.length) := by
    convert pop_execution program heap (base + 1) x0 x1 count x3 directoryEnd 3
        (word width sourceEnd :: stack) output (by omega)
        (by simpa using block 1 (by simp)) using 1 <;>
      simp only [put3_at, List.length_cons, Nat.add_assoc] <;> omega
  have t2 : Execution program
      (atState heap (base + 2) x0 x1 count directoryEnd (word width sourceEnd :: stack) output)
      (atState heap (base + 3) sourceEnd x1 count directoryEnd stack output)
      1 (6 + heap.size + stack.length + output.length) := by
    simpa only [put0_at, Nat.add_assoc] using pop_execution program heap (base + 2) x0 x1 count directoryEnd sourceEnd 0
      stack output (by omega) (by simpa using block 2 (by simp))
  convert (t0.append t1).append t2 using 1 <;>
    simp only [Nat.max_eq_left (by omega : 7 + heap.size + stack.length + output.length ≤
      8 + heap.size + stack.length + output.length),
      Nat.max_eq_left (by omega : 6 + heap.size + stack.length + output.length ≤
      8 + heap.size + stack.length + output.length)]

/-- Re-saving count after recovering the two endpoints keeps it available
through the boundary arithmetic, which uses register two as scratch. -/
theorem restore_preserving_execution (program : Program width 4) (heap : Array (Word width))
    (base x0 x1 x2 x3 count directoryEnd sourceEnd : ℕ) (stack output : List (Word width))
    (fits : base + 4 < 2 ^ width) (block : BlockAt program base [.pop 2, .pop 3, .pop 0, .push 2]) :
    Execution program
      (atState heap base x0 x1 x2 x3
        (word width count :: word width directoryEnd :: word width sourceEnd :: stack) output)
      (atState heap (base + 4) sourceEnd x1 count directoryEnd (word width count :: stack) output)
      4 (8 + heap.size + stack.length + output.length) := by
  have whole : BlockAt program base ([.pop 2, .pop 3, .pop 0] ++ [.push 2]) := block
  have first := restore_endpoints_execution program heap base x0 x1 x2 x3 count directoryEnd sourceEnd stack output
    (by omega) (BlockAt.prefix program base _ _ whole)
  have tail : BlockAt program (base + 3) [.push 2] := by
    simpa using BlockAt.suffix program base [.pop 2, .pop 3, .pop 0] [.push 2] whole
  have second := push2_execution program heap (base + 3) sourceEnd x1 count directoryEnd stack output
    (by omega) (by simpa using tail 0 (by simp))
  convert first.append second using 1 <;>
    simp only [Nat.add_assoc, Nat.max_eq_left (by omega :
      6 + heap.size + stack.length + output.length ≤ 8 + heap.size + stack.length + output.length)] <;> omega

private theorem put1_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 1 (word width value) =
      atState heap cursor x0 value x2 x3 stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

def arithmeticCode (width : ℕ) : Code width :=
  [.constant 1 (word width 0), .load 1 1, .add 1 1 1, .add 1 0 1,
   .constant 2 (word width (2 ^ width - 1)), .add 3 3 2, .add 3 3 2]

@[simp] theorem arithmeticCode_length : (arithmeticCode width).length = 7 := rfl

/-- New source boundaries are computed from the physically loaded channel
count. The reserved row address comes from the saved real directory endpoint. -/
theorem arithmetic_execution (program : Program width 4) (heap : Array (Word width))
    (base sourceEnd channels slot oldValue count : ℕ) (stack output : List (Word width))
    (nonempty : 0 < heap.size) (channelCell : heap[0]? = some (word width channels))
    (room : sourceEnd + 2 * channels < 2 ^ width) (slotFits : slot + 2 < 2 ^ width)
    (fits : base + 7 < 2 ^ width) (block : BlockAt program base (arithmeticCode width)) :
    Execution program (atState heap base sourceEnd oldValue count (slot + 2) stack output)
      (atState heap (base + 7) sourceEnd (sourceEnd + 2 * channels) (2 ^ width - 1) slot stack output)
      7 (5 + heap.size + stack.length + output.length) := by
  let mask := 2 ^ width - 1
  let s0 := atState heap base sourceEnd oldValue count (slot + 2) stack output
  let s1 := atState heap (base + 1) sourceEnd 0 count (slot + 2) stack output
  let s2 := atState heap (base + 2) sourceEnd channels count (slot + 2) stack output
  let s3 := atState heap (base + 3) sourceEnd (2 * channels) count (slot + 2) stack output
  let s4 := atState heap (base + 4) sourceEnd (sourceEnd + 2 * channels) count (slot + 2) stack output
  let s5 := atState heap (base + 5) sourceEnd (sourceEnd + 2 * channels) mask (slot + 2) stack output
  let s6 := atState heap (base + 6) sourceEnd (sourceEnd + 2 * channels) mask (slot + 1) stack output
  let s7 := atState heap (base + 7) sourceEnd (sourceEnd + 2 * channels) mask slot stack output
  have maskBound : mask < 2 ^ width := by have := Nat.two_pow_pos width; dsimp only [mask]; omega
  have maskWord : (word width mask).val = mask := Nat.mod_eq_of_lt maskBound
  have zeroWord : (word width 0).val = 0 := by simp [word]
  have channelWord : (word width channels).val = channels := Nat.mod_eq_of_lt (by omega)
  have doubledWord : (word width (2 * channels)).val = 2 * channels := Nat.mod_eq_of_lt (by omega)
  have sourceWord : (word width sourceEnd).val = sourceEnd := Nat.mod_eq_of_lt (by omega)
  have slotTwoWord : (word width (slot + 2)).val = slot + 2 := Nat.mod_eq_of_lt slotFits
  have slotOneWord : (word width (slot + 1)).val = slot + 1 := Nat.mod_eq_of_lt (by omega)
  have decrement (value : ℕ) : word width (value + 1 + mask) = word width value := by
    have same : value + 1 + mask = value + 2 ^ width := by have := Nat.two_pow_pos width; dsimp only [mask]; omega
    apply Fin.ext
    simp only [word, same, Nat.add_mod_right]
  have actual : heap[0] = word width channels := by
    rw [Array.getElem?_eq_getElem nonempty] at channelCell
    exact Option.some.inj channelCell
  have t0 : programStep program s0 = some s1 := by
    rw [fetched program s0 base (.constant 1 (word width 0)) rfl (by omega)
      (by simpa [arithmeticCode] using block 0 (by simp [arithmeticCode]))]
    change some (s0.advance.put 1 (word width 0)) = some s1
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put1_at]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.load 1 1) rfl (by omega)
      (by simpa [arithmeticCode] using block 1 (by simp [arithmeticCode]))]
    change (if h : (word width 0).val < heap.size then
      some (s1.advance.put 1 heap[(word width 0).val]) else none) = some s2
    rw [zeroWord, dite_eq_left nonempty, actual, advance_at _ _ _ _ _ _ _ _ (by omega), put1_at]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (base + 2) (.add 1 1 1) rfl (by omega)
      (by simpa [arithmeticCode] using block 2 (by simp [arithmeticCode]))]
    change some (s2.advance.put 1 (word width ((word width channels).val + (word width channels).val))) = some s3
    rw [channelWord, show channels + channels = 2 * channels from by omega,
      advance_at _ _ _ _ _ _ _ _ (by omega), put1_at]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (base + 3) (.add 1 0 1) rfl (by omega)
      (by simpa [arithmeticCode] using block 3 (by simp [arithmeticCode]))]
    change some (s3.advance.put 1 (word width ((word width sourceEnd).val + (word width (2 * channels)).val))) = some s4
    rw [sourceWord, doubledWord, advance_at _ _ _ _ _ _ _ _ (by omega), put1_at]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (base + 4) (.constant 2 (word width mask)) rfl (by omega)
      (by simpa [arithmeticCode, mask] using block 4 (by simp [arithmeticCode]))]
    change some (s4.advance.put 2 (word width mask)) = some s5
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put2_at]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (base + 5) (.add 3 3 2) rfl (by omega)
      (by simpa [arithmeticCode] using block 5 (by simp [arithmeticCode]))]
    change some (s5.advance.put 3 (word width ((word width (slot + 2)).val + (word width mask).val))) = some s6
    rw [slotTwoWord, maskWord, show slot + 2 = (slot + 1) + 1 from by omega,
      decrement, advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t6 : programStep program s6 = some s7 := by
    rw [fetched program s6 (base + 6) (.add 3 3 2) rfl (by omega)
      (by simpa [arithmeticCode] using block 6 (by simp [arithmeticCode]))]
    change some (s6.advance.put 3 (word width ((word width (slot + 1)).val + (word width mask).val))) = some s7
    rw [slotOneWord, maskWord, decrement, advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have first : Execution program s0 s4 4 (5 + heap.size + stack.length + output.length) := by
    convert Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.refl s4)))) using 1 <;>
      simp only [s0, s1, s2, s3, s4, atState, State.liveWords, Nat.max_self] <;> omega
  have last : Execution program s4 s7 3 (5 + heap.size + stack.length + output.length) := by
    convert Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.refl s7))) using 1 <;>
      simp only [s4, s5, s6, s7, atState, State.liveWords, Nat.max_self] <;> omega
  convert first.append last using 1 <;> simp only [Nat.max_self] <;> omega

/-- The full covered preparation restores endpoints, protects c, reads n,
and derives the two new directory cursors with eleven actual instructions. -/
theorem covered_prepare_execution (program : Program width 4) (heap : Array (Word width))
    (base channels slot sourceEnd x0 x1 x2 x3 count : ℕ) (stack output : List (Word width))
    (nonempty : 0 < heap.size) (channelCell : heap[0]? = some (word width channels))
    (room : sourceEnd + 2 * channels < 2 ^ width) (slotFits : slot + 2 < 2 ^ width)
    (fits : base + 11 < 2 ^ width) (block : BlockAt program base (coveredPrepareCode width)) :
    Execution program
      (atState heap base x0 x1 x2 x3
        (word width count :: word width (slot + 2) :: word width sourceEnd :: stack) output)
      (atState heap (base + 11) sourceEnd (sourceEnd + 2 * channels) (2 ^ width - 1) slot
        (word width count :: stack) output)
      11 (8 + heap.size + stack.length + output.length) := by
  have whole : BlockAt program base ([.pop 2, .pop 3, .pop 0, .push 2] ++ arithmeticCode width) := block
  have first := restore_preserving_execution program heap base x0 x1 x2 x3 count (slot + 2) sourceEnd
    stack output (by omega) (BlockAt.prefix program base _ _ whole)
  have tail : BlockAt program (base + 4) (arithmeticCode width) := by
    simpa using BlockAt.suffix program base [.pop 2, .pop 3, .pop 0, .push 2] _ whole
  have last := arithmetic_execution program heap (base + 4) sourceEnd channels slot x1 count
    (word width count :: stack) output nonempty channelCell room slotFits (by omega) tail
  convert first.append last using 1 <;>
    simp only [List.length_cons, Nat.add_assoc] <;> omega

/-- Actual add/copy recovers the activated directory endpoint after writing
its two reserved boundary cells. -/
theorem directory_finish_execution (program : Program width 4) (heap : Array (Word width))
    (base slot sourceEnd newEnd : ℕ) (stack output : List (Word width))
    (slotFits : slot + 2 < 2 ^ width) (fits : base + 2 < 2 ^ width)
    (block : BlockAt program base [.add 3 3 2, .copy 0 3]) :
    Execution program (atState heap base sourceEnd newEnd 1 (slot + 1) stack output)
      (atState heap (base + 2) (slot + 2) newEnd 1 (slot + 2) stack output)
      2 (5 + heap.size + stack.length + output.length) := by
  let s0 := atState heap base sourceEnd newEnd 1 (slot + 1) stack output
  let s1 := atState heap (base + 1) sourceEnd newEnd 1 (slot + 2) stack output
  let s2 := atState heap (base + 2) (slot + 2) newEnd 1 (slot + 2) stack output
  have t0 : programStep program s0 = some s1 := by
    rw [fetched program s0 base (.add 3 3 2) rfl (by omega) (by simpa using block 0 (by simp))]
    change some (s0.advance.put 3 (word width ((word width (slot + 1)).val + (word width 1).val))) = some s1
    rw [show (word width (slot + 1)).val = slot + 1 from Nat.mod_eq_of_lt (by omega),
      show (word width 1).val = 1 from Nat.mod_eq_of_lt (by omega),
      advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.copy 0 3) rfl (by omega) (by simpa using block 1 (by simp))]
    change some (s1.advance.put 0 (word width (slot + 2))) = some s2
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  convert Execution.cons t0 (Execution.cons t1 (Execution.refl s2)) using 1 <;>
    simp only [s0, s1, s2, atState, State.liveWords, Nat.max_self] <;> omega

/-- Complete covered suffix executes the actual channel pair loop, installs
its row and headers, physically recovers c, and jumps to the hot continuation. -/
theorem covered_execution (program : Program width 4) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient)
    (represented : Represented heap layout state)
    (base recordHeader endHeader returnPC sourceEnd slot channels scratch : ℕ)
    (stack output : List (Word width)) (within : channels ≤ ambient)
    (covered : ∀ channel : Fin channels,
      state.slots[(⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ : Fin ambient).val] ≠ 0)
    (nonempty : 0 < heap.size) (channelCell : heap[0]? = some (word width channels))
    (recordValid : recordHeader < heap.size) (endValid : endHeader < heap.size)
    (recordFits : recordHeader < 2 ^ width) (endFits : endHeader < 2 ^ width)
    (reserved : slot + 1 < heap.size) (slotFits : slot + 2 < 2 ^ width)
    (room : heap.size + 2 * channels < 2 ^ width) (sourceBefore : sourceEnd ≤ heap.size)
    (ambientFits : ambient + 1 < 2 ^ width) (fits : base + 38 < 2 ^ width)
    (block : BlockAt program base (coveredCode width base recordHeader endHeader returnPC)) :
    let pairs := ForestZeroPositive.pairHeap heap (ForestZeroPositive.channelLabels state channels)
    let installed := boundaryHeap pairs slot sourceEnd (sourceEnd + 2 * channels)
    let final := activeHeap installed recordHeader endHeader (sourceEnd + 2 * channels) (slot + 2)
    ∃ ticks peak, Execution program
      (atState heap base 0 scratch (layout.tableBase + channels) 0
        (word width state.coordinates.size :: word width (slot + 2) :: word width sourceEnd :: stack) output)
      (atState final returnPC (slot + 2) (sourceEnd + 2 * channels) state.coordinates.size 0 stack output)
      ticks peak ∧ ticks = 12 * channels + 27 ∧ ticks ≤ 12 * state.coordinates.size + 27 ∧
      peak ≤ 8 + heap.size + 2 * channels + stack.length + output.length := by
  let labels := ForestZeroPositive.channelLabels state channels
  let pairs := ForestZeroPositive.pairHeap heap labels
  let installed := boundaryHeap pairs slot sourceEnd (sourceEnd + 2 * channels)
  let final := activeHeap installed recordHeader endHeader (sourceEnd + 2 * channels) (slot + 2)
  let positive := ForestZeroPositive.fullCode width base
  let prepare := coveredPrepareCode width
  let boundaries := boundaryCode width
  let finish : Code width := [.add 3 3 2, .copy 0 3]
  let headers := activeCode width recordHeader endHeader
  let pop : Code width := [.pop 2]
  let jump := jumpCode width returnPC
  have whole : BlockAt program base (positive ++ (prepare ++ (boundaries ++ (finish ++ (headers ++ (pop ++ jump)))))) := by
    simpa only [coveredCode, List.append_assoc] using block
  have positiveBlock := BlockAt.prefix program base _ _ whole
  have afterPositive : BlockAt program (base + 14) (prepare ++ (boundaries ++ (finish ++ (headers ++ (pop ++ jump))))) := by
    simpa only [positive, ForestZeroPositive.fullCode_length] using BlockAt.suffix program base _ _ whole
  have prepareBlock := BlockAt.prefix program (base + 14) _ _ afterPositive
  have afterPrepare : BlockAt program (base + 25) (boundaries ++ (finish ++ (headers ++ (pop ++ jump)))) := by
    simpa only [prepare, coveredPrepareCode_length, Nat.add_assoc] using BlockAt.suffix program (base + 14) _ _ afterPositive
  have boundaryBlock := BlockAt.prefix program (base + 25) _ _ afterPrepare
  have afterBoundaries : BlockAt program (base + 29) (finish ++ (headers ++ (pop ++ jump))) := by
    simpa only [boundaries, boundaryCode_length, Nat.add_assoc] using BlockAt.suffix program (base + 25) _ _ afterPrepare
  have finishBlock := BlockAt.prefix program (base + 29) _ _ afterBoundaries
  have afterFinish : BlockAt program (base + 31) (headers ++ (pop ++ jump)) := by
    simpa only [finish, List.length_cons, List.length_nil, Nat.add_assoc] using BlockAt.suffix program (base + 29) _ _ afterBoundaries
  have headerBlock := BlockAt.prefix program (base + 31) _ _ afterFinish
  have afterHeaders : BlockAt program (base + 35) (pop ++ jump) := by
    simpa only [headers, activeCode_length, Nat.add_assoc] using BlockAt.suffix program (base + 31) _ _ afterFinish
  have popBlock := BlockAt.prefix program (base + 35) _ _ afterHeaders
  have jumpBlock : BlockAt program (base + 36) jump := by
    simpa only [pop, List.length_cons, List.length_nil, Nat.add_assoc] using BlockAt.suffix program (base + 35) _ _ afterHeaders
  obtain ⟨positiveTrace, positiveBound⟩ := ForestZeroPositive.loaded_allcovered_execution program heap layout state represented channels
    base scratch within covered
    (word width state.coordinates.size :: word width (slot + 2) :: word width sourceEnd :: stack) output ambientFits nonempty channelCell room (by omega) positiveBlock
  have pairSize : pairs.size = heap.size + 2 * channels := by
    simp only [pairs, ForestZeroPositive.pairHeap_size, labels, ForestZeroPositive.channelLabels_length]
  have retainedChannel : pairs[0]? = some (word width channels) :=
    (pairHeap_prefix heap labels 0 nonempty).trans channelCell
  have prepareTrace := covered_prepare_execution program pairs (base + 14) channels slot sourceEnd 0
    (ForestZeroPositive.lastScratch scratch labels) layout.tableBase 0 state.coordinates.size stack output
    (by rw [pairSize]; omega) retainedChannel (by omega) slotFits (by omega) prepareBlock
  have boundaryTrace := boundary_execution program pairs (base + 25) slot sourceEnd (sourceEnd + 2 * channels)
    (2 ^ width - 1) (word width state.coordinates.size :: stack) output
    (by rw [pairSize]; omega) (by omega) (by omega) boundaryBlock
  have finishTrace := directory_finish_execution program installed (base + 29) slot sourceEnd (sourceEnd + 2 * channels)
    (word width state.coordinates.size :: stack) output slotFits (by omega) finishBlock
  have installedSize : installed.size = heap.size + 2 * channels := by simp only [installed, boundaryHeap_size, pairSize]
  have headerTrace := active_execution program installed (base + 31) recordHeader endHeader (sourceEnd + 2 * channels)
    (slot + 2) 1 (slot + 2) (word width state.coordinates.size :: stack) output
    (by rw [installedSize]; omega) (by rw [installedSize]; omega) recordFits endFits (by omega) headerBlock
  have finalSize : final.size = heap.size + 2 * channels := by simp only [final, activeHeap_size, installedSize]
  have popTrace : Execution program
      (atState final (base + 35) (slot + 2) (sourceEnd + 2 * channels) 1 endHeader (word width state.coordinates.size :: stack) output)
      (atState final (base + 36) (slot + 2) (sourceEnd + 2 * channels) state.coordinates.size endHeader stack output)
      1 (6 + final.size + stack.length + output.length) := by
    simpa only [put2_at, Nat.add_assoc] using pop_execution program final (base + 35) (slot + 2)
      (sourceEnd + 2 * channels) 1 endHeader state.coordinates.size 2 stack output (by omega)
      (by simpa [pop] using popBlock 0 (by simp [pop]))
  have jumpTrace := jump_execution program final (base + 36) returnPC (slot + 2) (sourceEnd + 2 * channels)
    state.coordinates.size endHeader stack output (by omega) jumpBlock
  have joined := (((((positiveTrace.append prepareTrace).append boundaryTrace).append finishTrace).append headerTrace).append popTrace).append jumpTrace
  refine ⟨12 * channels + 27, 8 + heap.size + 2 * channels + stack.length + output.length, ?_, rfl, ?_, le_rfl⟩
  · convert joined using 1 <;> (try simp only [List.length_cons, Nat.add_assoc]) <;> omega
  · have actual := ForestZeroPositive.covered_count state represented.coherent channels within covered
    omega

/-- The unused branch deactivates the reserved row by actual modular pointer
arithmetic and two copies, leaving the saved source endpoint unchanged. -/
theorem unused_arithmetic_execution (program : Program width 4) (heap : Array (Word width))
    (base slot sourceEnd oldValue count : ℕ) (stack output : List (Word width))
    (slotFits : slot + 2 < 2 ^ width) (fits : base + 5 < 2 ^ width)
    (block : BlockAt program base
      [.constant 1 (word width (2 ^ width - 1)), .add 3 3 1, .add 3 3 1, .copy 1 0, .copy 0 3]) :
    Execution program (atState heap base sourceEnd oldValue count (slot + 2) stack output)
      (atState heap (base + 5) slot sourceEnd count slot stack output)
      5 (5 + heap.size + stack.length + output.length) := by
  let mask := 2 ^ width - 1
  let s0 := atState heap base sourceEnd oldValue count (slot + 2) stack output
  let s1 := atState heap (base + 1) sourceEnd mask count (slot + 2) stack output
  let s2 := atState heap (base + 2) sourceEnd mask count (slot + 1) stack output
  let s3 := atState heap (base + 3) sourceEnd mask count slot stack output
  let s4 := atState heap (base + 4) sourceEnd sourceEnd count slot stack output
  let s5 := atState heap (base + 5) slot sourceEnd count slot stack output
  have maskWord : (word width mask).val = mask := Nat.mod_eq_of_lt (by have := Nat.two_pow_pos width; dsimp only [mask]; omega)
  have decrement (value : ℕ) : word width (value + 1 + mask) = word width value := by
    have same : value + 1 + mask = value + 2 ^ width := by have := Nat.two_pow_pos width; dsimp only [mask]; omega
    apply Fin.ext
    simp only [word, same, Nat.add_mod_right]
  have t0 : programStep program s0 = some s1 := by
    rw [fetched program s0 base (.constant 1 (word width mask)) rfl (by omega) (by simpa [mask] using block 0 (by simp))]
    change some (s0.advance.put 1 (word width mask)) = some s1
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put1_at]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.add 3 3 1) rfl (by omega) (by simpa using block 1 (by simp))]
    change some (s1.advance.put 3 (word width ((word width (slot + 2)).val + (word width mask).val))) = some s2
    rw [show (word width (slot + 2)).val = slot + 2 from Nat.mod_eq_of_lt slotFits, maskWord,
      show slot + 2 = (slot + 1) + 1 from by omega, decrement,
      advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (base + 2) (.add 3 3 1) rfl (by omega) (by simpa using block 2 (by simp))]
    change some (s2.advance.put 3 (word width ((word width (slot + 1)).val + (word width mask).val))) = some s3
    rw [show (word width (slot + 1)).val = slot + 1 from Nat.mod_eq_of_lt (by omega), maskWord,
      decrement, advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (base + 3) (.copy 1 0) rfl (by omega) (by simpa using block 3 (by simp))]
    change some (s3.advance.put 1 (word width sourceEnd)) = some s4
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put1_at]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (base + 4) (.copy 0 3) rfl (by omega) (by simpa using block 4 (by simp))]
    change some (s4.advance.put 0 (word width slot)) = some s5
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have first : Execution program s0 s3 3 (5 + heap.size + stack.length + output.length) := by
    convert Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl s3))) using 1 <;>
      simp only [s0, s1, s2, s3, atState, State.liveWords, Nat.max_self] <;> omega
  have last : Execution program s3 s5 2 (5 + heap.size + stack.length + output.length) := by
    convert Execution.cons t3 (Execution.cons t4 (Execution.refl s5)) using 1 <;>
      simp only [s3, s4, s5, atState, State.liveWords, Nat.max_self] <;> omega
  convert first.append last using 1 <;> simp only [Nat.max_self] <;> omega

/-- Unused coordinates skip pair emission. Only real header stores exclude
reserved empty row, and c is recovered from its preserved stack word. -/
theorem unused_execution (program : Program width 4) (heap : Array (Word width))
    (base recordHeader endHeader returnPC sourceEnd slot x0 x1 x2 count : ℕ)
    (stack output : List (Word width))
    (recordValid : recordHeader < heap.size) (endValid : endHeader < heap.size)
    (recordFits : recordHeader < 2 ^ width) (endFits : endHeader < 2 ^ width)
    (slotFits : slot + 2 < 2 ^ width) (fits : base + 14 < 2 ^ width)
    (block : BlockAt program base (unusedCode width recordHeader endHeader returnPC)) :
    Execution program
      (atState heap base x0 x1 x2 0
        (word width count :: word width (slot + 2) :: word width sourceEnd :: stack) output)
      (atState (activeHeap heap recordHeader endHeader sourceEnd slot)
        returnPC slot sourceEnd count 0 stack output)
      14 (8 + heap.size + stack.length + output.length) := by
  let restore : Code width := [.pop 2, .pop 3, .pop 0]
  let arithmetic : Code width := [.constant 1 (word width (2 ^ width - 1)), .add 3 3 1, .add 3 3 1, .copy 1 0, .copy 0 3]
  let headers := activeCode width recordHeader endHeader
  let jump := jumpCode width returnPC
  have whole : BlockAt program base (restore ++ (arithmetic ++ (headers ++ jump))) := block
  have firstBlock := BlockAt.prefix program base _ _ whole
  have afterRestore : BlockAt program (base + 3) (arithmetic ++ (headers ++ jump)) := by
    simpa only [restore, List.length_cons, List.length_nil] using BlockAt.suffix program base _ _ whole
  have arithmeticBlock := BlockAt.prefix program (base + 3) _ _ afterRestore
  have afterArithmetic : BlockAt program (base + 8) (headers ++ jump) := by
    simpa only [arithmetic, List.length_cons, List.length_nil, Nat.add_assoc] using BlockAt.suffix program (base + 3) _ _ afterRestore
  have headersBlock := BlockAt.prefix program (base + 8) _ _ afterArithmetic
  have jumpBlock : BlockAt program (base + 12) jump := by
    simpa only [headers, activeCode_length, Nat.add_assoc] using BlockAt.suffix program (base + 8) _ _ afterArithmetic
  have first := restore_endpoints_execution program heap base x0 x1 x2 0 count (slot + 2) sourceEnd stack output (by omega) firstBlock
  have second := unused_arithmetic_execution program heap (base + 3) slot sourceEnd x1 count stack output slotFits (by omega) arithmeticBlock
  have third := active_execution program heap (base + 8) recordHeader endHeader sourceEnd slot count slot stack output
    recordValid endValid recordFits endFits (by omega) headersBlock
  have last := jump_execution program (activeHeap heap recordHeader endHeader sourceEnd slot) (base + 12) returnPC
    slot sourceEnd count endHeader stack output (by omega) jumpBlock
  convert ((first.append second).append third).append last using 1 <;>
    simp only [Nat.add_assoc, activeHeap_size] <;> omega

/-- Complete optional-row machine execution. The fetched search dispatches to
an actual positive-row emitter or to deactivation of the reserved row. Both
branches physically restore the same allocator count and caller stack. -/
theorem execution (program : Program width 4) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient)
    (represented : Represented heap layout state)
    (base recordHeader endHeader returnPC sourceEnd slot channels input scratch : ℕ)
    (stack output : List (Word width)) (within : channels ≤ ambient)
    (nonempty : 0 < heap.size) (channelCell : heap[0]? = some (word width channels))
    (recordValid : recordHeader < heap.size) (endValid : endHeader < heap.size)
    (recordFits : recordHeader < 2 ^ width) (endFits : endHeader < 2 ^ width)
    (sourceCell : heap[recordHeader]? = some (word width sourceEnd))
    (directoryCell : heap[endHeader]? = some (word width (slot + 2)))
    (reserved : slot + 1 < heap.size) (slotFits : slot + 2 < 2 ^ width)
    (sourceBefore : sourceEnd ≤ heap.size) (room : heap.size + 2 * channels < 2 ^ width)
    (ambientFits : ambient + 1 < 2 ^ width) (fits : base + 81 < 2 ^ width)
    (block : BlockAt program base (code width base recordHeader endHeader returnPC)) :
    let result := ForestZeroNonempty.search state (state.coordinates.size + 1) channels 0
    let covered := result.reason = .covered
    let pairs := ForestZeroPositive.pairHeap heap (ForestZeroPositive.channelLabels state channels)
    let installed := boundaryHeap pairs slot sourceEnd (sourceEnd + 2 * channels)
    let final := if covered then activeHeap installed recordHeader endHeader (sourceEnd + 2 * channels) (slot + 2)
      else activeHeap heap recordHeader endHeader sourceEnd slot
    ∃ ticks peak, Execution program
      (atState heap base input layout.tableBase state.coordinates.size scratch stack output)
      (atState final returnPC (if covered then slot + 2 else slot)
        (if covered then sourceEnd + 2 * channels else sourceEnd) state.coordinates.size 0 stack output)
      ticks peak ∧ ticks ≤ 23 * state.coordinates.size + 58 ∧
      peak ≤ 8 + heap.size + 2 * state.coordinates.size + stack.length + output.length := by
  let result := ForestZeroNonempty.search state (state.coordinates.size + 1) channels 0
  obtain ⟨searchTicks, searchTrace, searchBound, notExhausted⟩ := search_dispatch_execution program heap layout state represented
    base recordHeader endHeader sourceEnd (slot + 2) channels input scratch stack output within nonempty channelCell
    recordValid endValid recordFits endFits sourceCell directoryCell (by omega) ambientFits fits block
  let callerPrefix := saveEndpointsCode width recordHeader endHeader ++ savedSearchCode width (base + 6) ++
    jumpCode width (base + 29) ++ jumpCode width (base + 67)
  let coveredBody := coveredCode width (base + 29) recordHeader endHeader returnPC
  let unusedBody := unusedCode width recordHeader endHeader returnPC
  have whole : BlockAt program base (callerPrefix ++ (coveredBody ++ unusedBody)) := by
    simpa only [callerPrefix, coveredBody, unusedBody, code, List.append_assoc] using block
  have afterPrefix : BlockAt program (base + 29) (coveredBody ++ unusedBody) := by
    simpa only [callerPrefix, List.length_append, saveEndpointsCode_length, savedSearchCode_length,
      jumpCode_length] using BlockAt.suffix program base _ _ whole
  have coveredBlock := BlockAt.prefix program (base + 29) _ _ afterPrefix
  have unusedBlock : BlockAt program (base + 67) unusedBody := by
    simpa only [coveredBody, coveredCode_length, Nat.add_assoc] using BlockAt.suffix program (base + 29) _ _ afterPrefix
  cases reasonEq : result.reason with
  | exhausted => exact False.elim (notExhausted reasonEq)
  | covered =>
    have stopped := ForestZeroNonempty.search_stop state (state.coordinates.size + 1) channels 0
    have markedEq : result.marked = channels := by simpa only [result, reasonEq] using stopped
    have outcome := ForestZeroNonempty.search_outcome state represented.coherent channels within
    have coveredSlots : ∀ channel : Fin channels,
        state.slots[(⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ : Fin ambient).val] ≠ 0 := by
      rcases outcome with unused | covered
      · have contradiction := unused.1
        rw [reasonEq] at contradiction
        cases contradiction
      · exact covered.2.2
    have coveredCount := ForestZeroPositive.covered_count state represented.coherent channels within coveredSlots
    obtain ⟨bodyTicks, bodyPeak, bodyTrace, exactTicks, bodyBound, peakBound⟩ := covered_execution program heap layout state represented
      (base + 29) recordHeader endHeader returnPC sourceEnd slot channels (state.coordinates.size + 1 - result.marked)
      stack output within coveredSlots nonempty channelCell recordValid endValid recordFits endFits reserved slotFits
      room sourceBefore ambientFits (by omega) coveredBlock
    have searchTrace' : Execution program
        (atState heap base input layout.tableBase state.coordinates.size scratch stack output)
        (atState heap (base + 29) 0 (state.coordinates.size + 1 - result.marked) (layout.tableBase + channels) 0
          (word width state.coordinates.size :: word width (slot + 2) :: word width sourceEnd :: stack) output)
        searchTicks (8 + heap.size + stack.length + output.length) := by
      simpa only [result, reasonEq, ite_true, markedEq, Nat.sub_self] using searchTrace
    refine ⟨searchTicks + bodyTicks, max (8 + heap.size + stack.length + output.length) bodyPeak, ?_, ?_, ?_⟩
    · simpa only [result, reasonEq, ite_true] using searchTrace'.append bodyTrace
    · have boundedSearch : searchTicks ≤ 11 * (state.coordinates.size + 1) + 20 :=
        searchBound.trans (by have := min_le_right channels (state.coordinates.size + 1); omega)
      omega
    · apply Nat.max_le.mpr
      constructor <;> omega
  | unused =>
    have bodyTrace := unused_execution program heap (base + 67) recordHeader endHeader returnPC sourceEnd slot
      (channels - result.marked) (state.coordinates.size + 1 - result.marked) (layout.tableBase + result.marked)
      state.coordinates.size stack output recordValid endValid recordFits endFits slotFits (by omega) unusedBlock
    have searchTrace' : Execution program
        (atState heap base input layout.tableBase state.coordinates.size scratch stack output)
        (atState heap (base + 67) (channels - result.marked) (state.coordinates.size + 1 - result.marked)
          (layout.tableBase + result.marked) 0
          (word width state.coordinates.size :: word width (slot + 2) :: word width sourceEnd :: stack) output)
        searchTicks (8 + heap.size + stack.length + output.length) := by
      simpa only [result, reasonEq, reduceCtorEq, ite_false] using searchTrace
    refine ⟨searchTicks + 14, 8 + heap.size + stack.length + output.length, ?_, ?_, by omega⟩
    · simpa only [result, reasonEq, reduceCtorEq, ite_false, Nat.max_self] using searchTrace'.append bodyTrace
    · have boundedSearch : searchTicks ≤ 11 * (state.coordinates.size + 1) + 20 :=
        searchBound.trans (by have := min_le_right channels (state.coordinates.size + 1); omega)
      omega

/-- Dropping the reserved final row retains the actual original directory and
source words; no clause is reconstructed from an abstract model. -/
theorem Stored.original (rows : List (Clause (Fin locals))) (last : Clause (Fin locals))
    (directory source : ℕ) (heap : Array (Word width))
    (stored : Stored (rows ++ [last]) directory source heap) :
    Stored rows directory source heap := by
  have offsets (index : ℕ) (within : index ≤ rows.length) :
      sourceOffset (rows ++ [last]) source index = sourceOffset rows source index := by
    unfold sourceOffset
    rw [List.take_append, Nat.sub_eq_zero_of_le within]
    simp
  refine ⟨?_, ?_, ?_⟩
  · have := stored.fits
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    omega
  · intro index
    have extended : index.val < (rows ++ [last]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      have := index.isLt
      omega
    have original := stored.entry ⟨index.val, extended⟩
    simpa only [offsets index.val (Nat.le_of_lt index.isLt),
      offsets (index.val + 1) (by have := index.isLt; omega)] using original
  · intro index
    have extended : index.val < (rows ++ [last]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      have := index.isLt
      omega
    have original := stored.literals ⟨index.val, extended⟩
    simpa only [List.getElem_append_left index.isLt,
      offsets index.val (Nat.le_of_lt index.isLt)] using original

/-- All original packet cells survive the actual source-occurrence emitter,
including the channel header read by the later nonemptiness dispatcher. -/
private theorem occurrences_source (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient)
    (input scratch : ℕ) (references : List (Reference ambient))
    (sourceEnd : ℕ) (beforeTable : sourceEnd ≤ layout.tableBase)
    (beforeInverse : sourceEnd ≤ layout.inverseBase)
    (address : ℕ) (valid : address < sourceEnd) (bound : sourceEnd ≤ heap.size) :
    (Controller.Cost.ForestZeroEmit.emitReferences heap layout state input scratch references).heap[address]? =
      heap[address]? := by
  induction references generalizing heap state input scratch with
  | nil => rfl
  | cons reference rest ih =>
    have first := Controller.Cost.ForestZeroEmit.literal_source_frame heap layout state
      (reference.coordinate, reference.positive) sourceEnd beforeTable beforeInverse address valid bound
    have tail := ih
      (Controller.Cost.ForestZeroRows.literalHeap heap layout state (reference.coordinate, reference.positive))
      (Controller.Cost.ForestZeroRows.literalLayout heap layout state (reference.coordinate, reference.positive))
      (touch state reference.coordinate).1 (touch state reference.coordinate).2.1
      (if reference.positive then 1 else 0) beforeTable beforeInverse
      (by rw [Controller.Cost.ForestZeroRows.literalHeap_size]; omega)
    exact tail.trans first

/-- The physical reserved-row constructor uses the same immutable source
occurrences; the empty row contributes directory cells but no pair cells. -/
def reservedReferences (references : List (List (Reference ambient))) := references ++ [[]]

@[simp] theorem reservedReferences_length (references : List (List (Reference ambient))) :
    (reservedReferences references).length = references.length + 1 := by
  simp [reservedReferences]

@[simp] theorem reservedReferences_flatten (references : List (List (Reference ambient))) :
    (reservedReferences references).flatten = references.flatten := by
  simp [reservedReferences]

/-- Original packet words remain physically available after header, directory,
signed-pair emission and the local-count store. -/
theorem query_original_cell (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (references : List (List (Reference ambient)))
    (scratch sourceEnd address : ℕ) (beforeTable : sourceEnd ≤ layout.tableBase)
    (beforeInverse : sourceEnd ≤ layout.inverseBase) (valid : address < sourceEnd)
    (sourceBound : sourceEnd ≤ heap.size) :
    (ForestZeroQueryCaller.queryHeap heap layout state references scratch)[address]? = heap[address]? := by
  let head := ForestZeroQueryCaller.headerHeap width heap references.length references.flatten.length
  let headLayout := ForestZeroQueryCaller.headerLayout heap layout references.length references.flatten.length
  let rows := Controller.Cost.ForestZeroAssembly.originalRows references
  let source := head.size + 2 * rows.length
  let directory := Controller.Cost.ForestZeroDirectory.build head source state.coordinates.size rows
  let extended := Controller.Cost.ForestZeroAssembly.directoryLayout head headLayout source state.coordinates.size rows
  have old : address < heap.size := by omega
  have headOld : address < head.size := by dsimp only [head]; rw [ForestZeroQueryCaller.headerHeap_size]; omega
  have directoryOld : sourceEnd ≤ directory.heap.size := by
    dsimp only [directory]; rw [Controller.Cost.ForestZeroDirectory.build_size]
    dsimp only [head]; rw [ForestZeroQueryCaller.headerHeap_size]; omega
  have first := Controller.Cost.ForestZeroDirectory.build_prefix head source state.coordinates.size rows address headOld
  have emitted := occurrences_source directory.heap extended state directory.cursor scratch references.flatten
    sourceEnd beforeTable beforeInverse address valid directoryOld
  have retained : (ForestZeroQueryCaller.queryEmission heap layout state references scratch).heap[address]? = heap[address]? :=
    emitted.trans (first.trans
      (Controller.Cost.ForestCursorMaterialize.allocatedHeap_prefix width heap
        (ForestZeroQueryCaller.headerValues heap.size references.length references.flatten.length) address old))
  unfold ForestZeroQueryCaller.queryHeap
  rw [Array.getElem?_set_ne _ (by omega)]
  exact retained

/-- Query allocation keeps the dictionary at its original physical bases. -/
def constructedLayout (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (references : List (List (Reference ambient))) (scratch : ℕ) :
    Layout ambient (ForestZeroQueryCaller.queryHeap heap layout state references scratch).size where
  tableBase := layout.tableBase
  inverseBase := layout.inverseBase
  tableBound := by rw [ForestZeroQueryCaller.queryHeap_size]; have := layout.tableBound; omega
  inverseBound := by rw [ForestZeroQueryCaller.queryHeap_size]; have := layout.inverseBound; omega
  disjoint := layout.disjoint

/-- The emitted dictionary, not a supplied local-ID map, is represented by the
constructed heap even after storing its actual count in the query header. -/
theorem constructed_represented (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (represented : Represented heap layout state)
    (references : List (List (Reference ambient))) (scratch : ℕ) :
    Represented (ForestZeroQueryCaller.queryHeap heap layout state references scratch)
      (constructedLayout heap layout state references scratch)
      (ForestZeroQueryCaller.queryEmission heap layout state references scratch).dictionary := by
  let head := ForestZeroQueryCaller.headerHeap width heap references.length references.flatten.length
  let headLayout := ForestZeroQueryCaller.headerLayout heap layout references.length references.flatten.length
  let rows := Controller.Cost.ForestZeroAssembly.originalRows references
  let source := head.size + 2 * rows.length
  let directory := Controller.Cost.ForestZeroDirectory.build head source state.coordinates.size rows
  let extended := Controller.Cost.ForestZeroAssembly.directoryLayout head headLayout source state.coordinates.size rows
  have directoryRep := Controller.Cost.ForestZeroAssembly.directory_represented head headLayout state
    (ForestZeroQueryCaller.header_represented heap layout state represented references.length references.flatten.length)
    source state.coordinates.size rows
  have actual := Controller.Cost.ForestZeroEmit.emitReferences_represented directory.heap extended state
    directoryRep directory.cursor scratch references.flatten
  have bases := Controller.Cost.ForestZeroEmit.emitReferences_bases directory.heap extended state
    directory.cursor scratch references.flatten
  let emitted := ForestZeroQueryCaller.queryEmission heap layout state references scratch
  have storeValid : heap.size + 1 < emitted.heap.size := by
    dsimp only [emitted]
    rw [ForestZeroQueryCaller.queryEmission_size]
    omega
  have actual' : Represented emitted.heap emitted.layout emitted.dictionary := actual
  have tableEq : emitted.layout.tableBase = layout.tableBase := bases.1
  have inverseEq : emitted.layout.inverseBase = layout.inverseBase := bases.2
  refine ⟨actual'.coherent, ?_, ?_⟩
  · intro coordinate
    have cell := actual'.slots coordinate
    rw [tableEq] at cell
    change ((emitted.heap.set (heap.size + 1) (word width emitted.dictionary.coordinates.size) storeValid)[layout.tableBase + coordinate.val]?) = _
    rw [Array.getElem?_set_ne _ (by have := layout.table_valid coordinate; omega)]
    exact cell
  · intro index coordinate present
    have cell := actual'.inverse index coordinate present
    rw [inverseEq] at cell
    have valid : index < ambient := lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp present).1
      (count_le_ambient emitted.dictionary actual'.coherent)
    change ((emitted.heap.set (heap.size + 1) (word width emitted.dictionary.coordinates.size) storeValid)[layout.inverseBase + index]?) = _
    rw [Array.getElem?_set_ne _ (by have := layout.inverse_valid index valid; omega)]
    exact cell

/-- The complete constructor executes the original occurrence emission, then
reads its own reserved endpoints and performs optional-row dispatch. It saves
and restores the actual emitted local count independently of inputHeader. -/
def constructorCode (width base protectedEnd recordHeader endHeader returnPC : ℕ)
    (references : List (List (Reference ambient))) : Code width :=
  let query := ForestZeroQueryCaller.queryCode width base protectedEnd (reservedReferences references)
  query ++ code width (base + query.length) recordHeader endHeader returnPC

theorem constructor_execution (program : Program width 4) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient)
    (represented : Represented heap layout state) (channels sourceEnd : ℕ)
    (references : List (List (Reference ambient)))
    (stored : ∀ reference ∈ references.flatten, Controller.Cost.ForestZeroEmit.StoredReference heap channels sourceEnd reference)
    (beforeTable : sourceEnd ≤ layout.tableBase) (beforeInverse : sourceEnd ≤ layout.inverseBase)
    (sourceBound : sourceEnd ≤ heap.size) (sourcePositive : 0 < sourceEnd)
    (channelCell : heap[0]? = some (word width channels)) (within : channels ≤ ambient)
    (base returnPC : ℕ) (stack output : List (Word width))
    (room : heap.size + 5 + 2 * (references.length + 1) + 2 * references.flatten.length + 2 * ambient < 2 ^ width)
    (ambientFits : ambient + 1 < 2 ^ width)
    (fits : base + (constructorCode width base heap.size heap.size (heap.size + 4) returnPC references).length < 2 ^ width)
    (block : BlockAt program base (constructorCode width base heap.size heap.size (heap.size + 4) returnPC references)) :
    let refs := reservedReferences references
    let prepared := ForestZeroQueryCaller.queryHeap heap layout state refs 0
    let emitted := ForestZeroQueryCaller.queryEmission heap layout state refs 0
    let result := ForestZeroNonempty.search emitted.dictionary (emitted.dictionary.coordinates.size + 1) channels 0
    let covered := result.reason = .covered
    let slot := heap.size + 5 + 2 * references.length
    let pairs := ForestZeroPositive.pairHeap prepared (ForestZeroPositive.channelLabels emitted.dictionary channels)
    let installed := boundaryHeap pairs slot prepared.size (prepared.size + 2 * channels)
    let final := if covered then activeHeap installed heap.size (heap.size + 4) (prepared.size + 2 * channels) (slot + 2)
      else activeHeap prepared heap.size (heap.size + 4) prepared.size slot
    ∃ ticks peak, Execution program
      (atState heap base (heap.size + 5 + 2 * (references.length + 1)) layout.tableBase state.coordinates.size 0
        (word width layout.inverseBase :: stack) output)
      (atState final returnPC (if covered then slot + 2 else slot)
        (if covered then prepared.size + 2 * channels else prepared.size) emitted.dictionary.coordinates.size 0
        (word width layout.inverseBase :: stack) output)
      ticks peak ∧ ticks ≤ 79 + 5 * references.length + 23 * references.flatten.length + 23 * emitted.dictionary.coordinates.size ∧
      peak ≤ 14 + heap.size + 2 * (references.length + 1) + 2 * references.flatten.length +
        2 * emitted.dictionary.coordinates.size + stack.length + output.length := by
  let refs := reservedReferences references
  let query := ForestZeroQueryCaller.queryCode width base heap.size refs
  let optionalBase := base + query.length
  let prepared := ForestZeroQueryCaller.queryHeap heap layout state refs 0
  let emitted := ForestZeroQueryCaller.queryEmission heap layout state refs 0
  let extended := constructedLayout heap layout state refs 0
  let slot := heap.size + 5 + 2 * references.length
  have lengths : (constructorCode width base heap.size heap.size (heap.size + 4) returnPC references).length = query.length + 81 := by
    simp only [constructorCode, query, refs, List.length_append, code_length]
  have queryBlock : BlockAt program base query := BlockAt.prefix program base _ _ block
  have optionalBlock : BlockAt program optionalBase (code width optionalBase heap.size (heap.size + 4) returnPC) :=
    BlockAt.suffix program base query _ block
  have preparedSize : prepared.size = heap.size + 5 + 2 * (references.length + 1) + 2 * references.flatten.length := by
    simp only [prepared, refs, ForestZeroQueryCaller.queryHeap_size,
      reservedReferences_length, reservedReferences_flatten]
  have actual := constructed_represented heap layout state represented refs 0
  have countBound := count_le_ambient emitted.dictionary actual.coherent
  have firstCell := ForestZeroQueryCaller.query_header_cell heap layout state represented refs 0 0 (by decide) (by decide)
  have lastCell := ForestZeroQueryCaller.query_header_cell heap layout state represented refs 0 4 (by decide) (by decide)
  have sourceCell : prepared[heap.size]? = some (word width prepared.size) := by
    simpa only [prepared, refs, ForestZeroQueryCaller.headerValues, reservedReferences_length,
      reservedReferences_flatten, List.getElem_cons_zero, Nat.add_zero, preparedSize] using firstCell
  have directoryCell : prepared[heap.size + 4]? = some (word width (slot + 2)) := by
    simpa [prepared, refs, slot, ForestZeroQueryCaller.headerValues, Nat.mul_add, Nat.add_assoc] using lastCell
  have preservedChannel : prepared[0]? = some (word width channels) :=
    (query_original_cell heap layout state refs 0 sourceEnd 0 beforeTable beforeInverse sourcePositive sourceBound).trans channelCell
  obtain ⟨queryTicks, queryPeak, queryTrace, queryBound, queryPeakBound⟩ :=
    ForestZeroQueryCaller.query_execution program heap layout state represented channels sourceEnd refs
      (by simpa only [refs, reservedReferences_flatten] using stored) beforeTable beforeInverse base stack output
      (by simp only [refs, reservedReferences_length, reservedReferences_flatten]; omega)
      ambientFits (by change base + query.length < 2 ^ width; omega) queryBlock
  obtain ⟨bodyTicks, bodyPeak, bodyTrace, bodyBound, bodyPeakBound⟩ := execution program prepared extended emitted.dictionary
    actual optionalBase heap.size (heap.size + 4) returnPC prepared.size slot channels (heap.size + 1) emitted.scratch
    (word width layout.inverseBase :: stack) output within (by rw [preparedSize]; omega) preservedChannel
    (by rw [preparedSize]; omega) (by rw [preparedSize]; omega) (by omega) (by omega)
    sourceCell directoryCell (by rw [preparedSize]; dsimp only [slot]; omega) (by dsimp only [slot]; omega)
    le_rfl (by rw [preparedSize]; omega) ambientFits (by omega) optionalBlock
  refine ⟨queryTicks + bodyTicks, max queryPeak bodyPeak, ?_, ?_, ?_⟩
  · simpa only [refs, reservedReferences_length, extended, constructedLayout, optionalBase, query,
      prepared, emitted, slot] using queryTrace.append bodyTrace
  · change queryTicks + bodyTicks ≤ 79 + 5 * references.length +
      23 * references.flatten.length + 23 * emitted.dictionary.coordinates.size
    simp only [refs, reservedReferences_length, reservedReferences_flatten] at queryBound
    omega
  · change max queryPeak bodyPeak ≤ 14 + heap.size + 2 * (references.length + 1) +
      2 * references.flatten.length + 2 * emitted.dictionary.coordinates.size + stack.length + output.length
    simp only [refs, reservedReferences_length, reservedReferences_flatten] at queryPeakBound
    simp only [List.length_cons] at bodyPeakBound
    rw [preparedSize] at bodyPeakBound
    exact Nat.max_le.mpr ⟨by omega, by omega⟩


/-- Retaining a directory prefix retains its original literal stream. -/
theorem Stored.take (rows : List (Clause (Fin locals))) (count directory source : ℕ)
    (heap : Array (Word width)) (stored : Stored rows directory source heap) :
    Stored (rows.take count) directory source heap := by
  have offset (index : ℕ) (within : index ≤ count) :
      sourceOffset (rows.take count) source index = sourceOffset rows source index := by
    unfold sourceOffset
    rw [List.take_take, Nat.min_eq_left within]
  refine ⟨?_, ?_, ?_⟩
  · have := stored.fits
    have := List.length_take_le' count rows
    omega
  · intro index
    have below : index.val < rows.length :=
      lt_of_lt_of_le index.isLt (List.length_take_le' count rows)
    have before : index.val + 1 ≤ count := by
      have := index.isLt
      simp only [List.length_take] at this
      omega
    simpa only [offset index.val (by omega), offset (index.val + 1) before] using
      stored.entry ⟨index.val, below⟩
  · intro index
    have below : index.val < rows.length :=
      lt_of_lt_of_le index.isLt (List.length_take_le' count rows)
    have before : index.val ≤ count := by
      have := index.isLt
      simp only [List.length_take] at this
      omega
    simpa only [List.getElem_take, offset index.val before] using stored.literals ⟨index.val, below⟩

/-- Typed rows come from the actual compiler over the reserved constructor;
the last empty row changes neither the literal stream nor the local IDs. -/
def reservedClauses (state : Dictionary ambient) (coherent : Coherent state)
    (references : List (List (Reference ambient))) :=
  ForestZeroAssembly.finiteClauses
    (compileRows state (ForestZeroAssembly.originalRows (reservedReferences references))).2.1
    (rows_bounds state coherent (ForestZeroAssembly.originalRows (reservedReferences references)))

theorem reservedClauses_profile (state : Dictionary ambient) (coherent : Coherent state)
    (references : List (List (Reference ambient))) :
    (reservedClauses state coherent references).map List.length =
      references.map List.length ++ [0] := by
  have finite := ForestZeroAssembly.finiteClauses_profile
    (compileRows state (ForestZeroAssembly.originalRows (reservedReferences references))).2.1
    (rows_bounds state coherent (ForestZeroAssembly.originalRows (reservedReferences references)))
  have original := rows_shape state (ForestZeroAssembly.originalRows (reservedReferences references))
  exact finite.trans (original.trans (by
    simp [ForestZeroAssembly.originalRows, reservedReferences, List.map_map, Function.comp_def]))

/-- The backend's original row prefix is obtained by truncating the actual
stored directory, not by supplying an independently chosen formula. -/
def originalClauses (state : Dictionary ambient) (coherent : Coherent state)
    (references : List (List (Reference ambient))) :=
  (reservedClauses state coherent references).take references.length

theorem originalClauses_profile (state : Dictionary ambient) (coherent : Coherent state)
    (references : List (List (Reference ambient))) :
    (originalClauses state coherent references).map List.length = references.map List.length := by
  unfold originalClauses
  rw [List.map_take, reservedClauses_profile]
  simp only [List.take_append, List.length_map, Nat.sub_self, List.take_zero,
    List.append_nil]
  exact List.take_of_length_le (by simp only [List.length_map]; exact le_rfl)

theorem originalClauses_length (state : Dictionary ambient) (coherent : Coherent state)
    (references : List (List (Reference ambient))) :
    (originalClauses state coherent references).length = references.length := by
  have same := congrArg List.length (originalClauses_profile state coherent references)
  simpa only [List.length_map] using same

/-- The original stream ends at the actual allocated heap end. The reserved
row occupies only its two directory words. -/
theorem originalClauses_end (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (coherent : Coherent state)
    (references : List (List (Reference ambient))) (scratch : ℕ) :
    sourceOffset (originalClauses state coherent references)
      (heap.size + 5 + 2 * (references.length + 1))
      (originalClauses state coherent references).length =
      (ForestZeroQueryCaller.queryHeap heap layout state (reservedReferences references) scratch).size := by
  unfold sourceOffset
  rw [List.take_length, originalClauses_profile, ForestZeroQueryCaller.queryHeap_size]
  simp only [reservedReferences_length, reservedReferences_flatten, List.length_flatten]

theorem reserved_query_stored (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (represented : Represented heap layout state)
    (references : List (List (Reference ambient))) (scratch : ℕ) :
    Stored (originalClauses state represented.coherent references) (heap.size + 5)
      (heap.size + 5 + 2 * (references.length + 1))
      (ForestZeroQueryCaller.queryHeap heap layout state (reservedReferences references) scratch) := by
  have actual := ForestZeroQueryCaller.query_stored heap layout state represented (reservedReferences references) scratch
  have retainedRows := Stored.take (reservedClauses state represented.coherent references)
    references.length (heap.size + 5) (heap.size + 5 + 2 * (references.length + 1))
    (ForestZeroQueryCaller.queryHeap heap layout state (reservedReferences references) scratch)
    (by simpa only [reservedClauses, reservedReferences_length] using actual)
  exact retainedRows

/-- Actual allocated channel IDs fit the same local finite domain as the
compiled rows. Coverage is used solely to show that subtraction removes a
positive encoded ID. -/
theorem positiveClause_bounded (state : Dictionary ambient) (coherent : Coherent state)
    (channels : ℕ) (within : channels ≤ ambient)
    (covered : ∀ channel : Fin channels,
      state.slots[(⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ : Fin ambient).val] ≠ 0) :
    ∀ literal ∈ ForestZeroPositive.positiveClause state channels,
      literal.1 < state.coordinates.size := by
  have labels : ∀ label ∈ ForestZeroPositive.channelLabels state channels,
      label < state.coordinates.size := by
    induction channels with
    | zero => simp [ForestZeroPositive.channelLabels]
    | succ count ih =>
      intro label present
      simp only [ForestZeroPositive.channelLabels, List.mem_cons] at present
      rcases present with rfl | tail
      · let coordinate : Fin ambient := ⟨count, by omega⟩
        have bounded := encoded_bound state coherent coordinate
        have positive := covered ⟨count, by omega⟩
        change state.slots[count] ≤ state.coordinates.size at bounded
        change state.slots[count] ≠ 0 at positive
        have valid : count < ambient := by omega
        simp only [ForestZeroNonempty.slotAt, dite_eq_left valid]
        change state.slots[count] - 1 < state.coordinates.size
        omega
      · exact ih (by omega) (fun channel => covered ⟨channel.val, by omega⟩) label tail
  intro literal present
  obtain ⟨label, member, equality⟩ := List.mem_map.mp present
  subst literal
  exact labels label member

/-- Canonical backend headers remain above the protected caller prefix.
The base is the actual emitted heap end, including a covered channel row. -/
def backendLayout (rows : List (Clause (Fin locals))) (protectedEnd source finish : ℕ)
    (directoryBound : protectedEnd + 5 + 2 * rows.length ≤ source)
    (streamBound : sourceOffset rows source rows.length ≤ finish) :
    Controller.Horn.SourceDirectory.Layout rows where
  directory := protectedEnd + 5
  source := source
  base := finish
  recordHeader := protectedEnd
  inputHeader := protectedEnd + 1
  firstHeader := protectedEnd + 2
  directoryHeader := protectedEnd + 3
  endHeader := protectedEnd + 4
  directoryBefore := directoryBound
  sourceBefore := streamBound
  headersBefore := by
    intro header member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> omega
  headersDistinct := by
    simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, and_true, or_false]
    omega


/-- The covered source installation is proved over an abstract emitted heap
and typed rows, avoiding reduction of the complete occurrence compiler. -/
theorem covered_backend_stored (compiled : Dictionary ambient) (coherent : Coherent compiled)
    (prepared : Array (Word width)) (rows : List (Clause (Fin compiled.coordinates.size)))
    (protectedEnd rowTotal channels : ℕ) (within : channels ≤ ambient)
    (slots : ∀ channel : Fin channels,
      compiled.slots[(⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ : Fin ambient).val] ≠ 0)
    (rowCount : rows.length = rowTotal)
    (old : Stored rows (protectedEnd + 5) (protectedEnd + 5 + 2 * (rowTotal + 1)) prepared)
    (streamEnd : sourceOffset rows (protectedEnd + 5 + 2 * (rowTotal + 1)) rows.length = prepared.size)
    (sourceBound : protectedEnd + 5 + 2 * (rowTotal + 1) ≤ prepared.size) :
    let source := protectedEnd + 5 + 2 * (rowTotal + 1)
    let slot := protectedEnd + 5 + 2 * rowTotal
    let pairs := ForestZeroPositive.pairHeap prepared (ForestZeroPositive.channelLabels compiled channels)
    let final := activeHeap (boundaryHeap pairs slot prepared.size (prepared.size + 2 * channels))
      protectedEnd (protectedEnd + 4) (prepared.size + 2 * channels) (slot + 2)
    ∃ clauses : List (Clause (Fin compiled.coordinates.size)),
      Stored clauses (protectedEnd + 5) source final ∧ clauses.length = rowTotal + 1 ∧
      sourceOffset clauses source clauses.length = final.size ∧
      ∃ backend : Controller.Horn.SourceDirectory.Layout clauses,
        backend.directory = protectedEnd + 5 ∧ backend.source = source ∧ backend.base = final.size ∧
        backend.recordHeader = protectedEnd ∧ backend.inputHeader = protectedEnd + 1 ∧
        backend.firstHeader = protectedEnd + 2 ∧ backend.directoryHeader = protectedEnd + 3 ∧
        backend.endHeader = protectedEnd + 4 := by
  let source := protectedEnd + 5 + 2 * (rowTotal + 1)
  let slot := protectedEnd + 5 + 2 * rowTotal
  let positive := ForestZeroPositive.positiveClause compiled channels
  have bounds : ∀ literal ∈ positive, literal.1 < compiled.coordinates.size :=
    positiveClause_bounded compiled coherent channels within slots
  let last := finiteClause positive bounds
  have raw : last.map (fun literal => (literal.1.val, literal.2)) =
      (ForestZeroPositive.channelLabels compiled channels).map (fun localIndex => (localIndex, true)) :=
    ForestZeroAssembly.finiteClause_raw positive bounds
  have lastLength : last.length = channels := by
    have equal := congrArg List.length raw
    simpa only [List.length_map, ForestZeroPositive.channelLabels_length] using equal
  let pairs := ForestZeroPositive.pairHeap prepared (ForestZeroPositive.channelLabels compiled channels)
  let installed := boundaryHeap pairs slot prepared.size (prepared.size + 2 * channels)
  let final := activeHeap installed protectedEnd (protectedEnd + 4) (prepared.size + 2 * channels) (slot + 2)
  have pairSize : pairs.size = prepared.size + 2 * channels := by
    simp only [pairs, ForestZeroPositive.pairHeap_size, ForestZeroPositive.channelLabels_length]
  have stored : Stored (rows ++ [last]) (protectedEnd + 5) source final := by
    have actual := installed_positive_active rows last
      (ForestZeroPositive.channelLabels compiled channels) prepared (protectedEnd + 5) source
      protectedEnd (protectedEnd + 4) old streamEnd
      (by dsimp only [source]; rw [rowCount]; omega)
      (by rw [rowCount]; omega) (by omega) (by omega)
      (by omega) (by omega) raw
    simpa only [pairSize, rowCount, slot, Nat.mul_add, Nat.mul_one, Nat.add_assoc,
      pairs, installed, final] using actual
  have endEq : sourceOffset (rows ++ [last]) source (rows ++ [last]).length = final.size := by
    have finalSize : final.size = prepared.size + 2 * channels := by
      simp only [final, activeHeap, installed, boundaryHeap_size,
        Array.size_setIfInBounds, pairSize]
    unfold sourceOffset at streamEnd ⊢
    rw [List.take_length, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [lastLength, finalSize]
    simp only [List.take_length] at streamEnd
    omega
  let backend := backendLayout (rows ++ [last]) protectedEnd source final.size
    (by dsimp only [source]; simp only [List.length_append, List.length_cons,
      List.length_nil, rowCount]; omega) endEq.le
  exact ⟨rows ++ [last], stored,
    by simp only [List.length_append, List.length_cons, List.length_nil, rowCount],
    endEq, backend, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Both dispatched branches produce a complete typed source directory and
its canonical backend layout. The unused branch omits the reserved empty row;
the covered branch installs the actual finite channel clause. -/
theorem constructor_backend_stored (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient)
    (represented : Represented heap layout state)
    (references : List (List (Reference ambient))) (channels scratch : ℕ)
    (within : channels ≤ ambient) :
    let refs := reservedReferences references
    let compiled := (compileRows state (ForestZeroAssembly.originalRows refs)).1
    let prepared := ForestZeroQueryCaller.queryHeap heap layout state refs scratch
    let result := ForestZeroNonempty.search compiled (compiled.coordinates.size + 1) channels 0
    let covered := result.reason = .covered
    let slot := heap.size + 5 + 2 * references.length
    let pairs := ForestZeroPositive.pairHeap prepared (ForestZeroPositive.channelLabels compiled channels)
    let installed := boundaryHeap pairs slot prepared.size (prepared.size + 2 * channels)
    let final := if covered then
      activeHeap installed heap.size (heap.size + 4) (prepared.size + 2 * channels) (slot + 2)
      else activeHeap prepared heap.size (heap.size + 4) prepared.size slot
    ∃ clauses : List (Clause (Fin compiled.coordinates.size)),
      Stored clauses (heap.size + 5) (heap.size + 5 + 2 * (references.length + 1)) final ∧
      clauses.length = (if covered then references.length + 1 else references.length) ∧
      sourceOffset clauses (heap.size + 5 + 2 * (references.length + 1)) clauses.length = final.size ∧
      ∃ backend : Controller.Horn.SourceDirectory.Layout clauses,
        backend.directory = heap.size + 5 ∧
        backend.source = heap.size + 5 + 2 * (references.length + 1) ∧
        backend.base = final.size ∧ backend.recordHeader = heap.size ∧
        backend.inputHeader = heap.size + 1 ∧ backend.firstHeader = heap.size + 2 ∧
        backend.directoryHeader = heap.size + 3 ∧ backend.endHeader = heap.size + 4 := by
  let refs := reservedReferences references
  let compiled := (compileRows state (ForestZeroAssembly.originalRows refs)).1
  let prepared := ForestZeroQueryCaller.queryHeap heap layout state refs scratch
  let rows := originalClauses state represented.coherent references
  let source := heap.size + 5 + 2 * (references.length + 1)
  let slot := heap.size + 5 + 2 * references.length
  let result := ForestZeroNonempty.search compiled (compiled.coordinates.size + 1) channels 0
  have coherent : Coherent compiled :=
    (rows_dictionary state represented.coherent (ForestZeroAssembly.originalRows refs)).1
  have old : Stored rows (heap.size + 5) source prepared :=
    reserved_query_stored heap layout state represented references scratch
  have rowCount : rows.length = references.length := originalClauses_length state represented.coherent references
  have streamEnd : sourceOffset rows source rows.length = prepared.size :=
    originalClauses_end heap layout state represented.coherent references scratch
  have size : prepared.size = heap.size + 5 + 2 * (references.length + 1) + 2 * references.flatten.length := by
    simp only [prepared, refs, ForestZeroQueryCaller.queryHeap_size,
      reservedReferences_length, reservedReferences_flatten]
  by_cases covered : result.reason = .covered
  · have outcome := ForestZeroNonempty.search_outcome compiled coherent channels within
    have slots : ∀ channel : Fin channels,
        compiled.slots[(⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ : Fin ambient).val] ≠ 0 := by
      rcases outcome with unused | allCovered
      · have contradiction := unused.1
        change result.reason = .unused at contradiction
        rw [covered] at contradiction
        cases contradiction
      · exact allCovered.2.2
    obtain ⟨clauses, stored, length, endEq, backend, fields⟩ := covered_backend_stored
      compiled coherent prepared rows heap.size references.length channels within slots rowCount old streamEnd
      (by rw [size]; omega)
    refine ⟨clauses, ?_, ?_, ?_, backend, ?_⟩
    · change Stored clauses (heap.size + 5) source
        (if result.reason = .covered then
          activeHeap (boundaryHeap (ForestZeroPositive.pairHeap prepared
            (ForestZeroPositive.channelLabels compiled channels)) slot prepared.size (prepared.size + 2 * channels))
            heap.size (heap.size + 4) (prepared.size + 2 * channels) (slot + 2)
          else activeHeap prepared heap.size (heap.size + 4) prepared.size slot)
      rw [ite_eq_left covered]
      exact stored
    · change clauses.length = if result.reason = .covered then references.length + 1 else references.length
      rw [ite_eq_left covered]
      exact length
    · change sourceOffset clauses source clauses.length =
        (if result.reason = .covered then
          activeHeap (boundaryHeap (ForestZeroPositive.pairHeap prepared
            (ForestZeroPositive.channelLabels compiled channels)) slot prepared.size (prepared.size + 2 * channels))
            heap.size (heap.size + 4) (prepared.size + 2 * channels) (slot + 2)
          else activeHeap prepared heap.size (heap.size + 4) prepared.size slot).size
      rw [ite_eq_left covered]
      exact endEq
    · rcases fields with ⟨directoryEq, sourceEq, baseEq, recordEq, inputEq, firstEq, directoryHeaderEq, endHeaderEq⟩
      refine ⟨directoryEq, sourceEq, ?_, recordEq, inputEq, firstEq, directoryHeaderEq, endHeaderEq⟩
      change backend.base = (if result.reason = .covered then
        activeHeap (boundaryHeap (ForestZeroPositive.pairHeap prepared
          (ForestZeroPositive.channelLabels compiled channels)) slot prepared.size (prepared.size + 2 * channels))
          heap.size (heap.size + 4) (prepared.size + 2 * channels) (slot + 2)
        else activeHeap prepared heap.size (heap.size + 4) prepared.size slot).size
      rw [ite_eq_left covered]
      exact baseEq
  · let final := activeHeap prepared heap.size (heap.size + 4) prepared.size slot
    have stored : Stored rows (heap.size + 5) source final :=
      stored_active old heap.size (heap.size + 4) prepared.size slot
        (by rw [size]; omega) (by rw [size]; omega) (by omega) (by omega)
        (by dsimp only [source]; omega)
    have endEq : sourceOffset rows source rows.length = final.size := by
      simpa only [final, activeHeap, Array.size_setIfInBounds] using streamEnd
    let backend := backendLayout rows heap.size source final.size
      (by dsimp only [source]; rw [rowCount]; omega) endEq.le
    refine ⟨rows, ?_, ?_, ?_, backend, ?_⟩
    · change Stored rows (heap.size + 5) source
        (if result.reason = .covered then
          activeHeap (boundaryHeap (ForestZeroPositive.pairHeap prepared
            (ForestZeroPositive.channelLabels compiled channels)) slot prepared.size (prepared.size + 2 * channels))
            heap.size (heap.size + 4) (prepared.size + 2 * channels) (slot + 2) else final)
      rw [ite_eq_right covered]
      exact stored
    · change rows.length = if result.reason = .covered then references.length + 1 else references.length
      rw [ite_eq_right covered]
      exact rowCount
    · change sourceOffset rows source rows.length =
        (if result.reason = .covered then
          activeHeap (boundaryHeap (ForestZeroPositive.pairHeap prepared
            (ForestZeroPositive.channelLabels compiled channels)) slot prepared.size (prepared.size + 2 * channels))
            heap.size (heap.size + 4) (prepared.size + 2 * channels) (slot + 2) else final).size
      rw [ite_eq_right covered]
      exact endEq
    · refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
      change backend.base = (if result.reason = .covered then
        activeHeap (boundaryHeap (ForestZeroPositive.pairHeap prepared
          (ForestZeroPositive.channelLabels compiled channels)) slot prepared.size (prepared.size + 2 * channels))
          heap.size (heap.size + 4) (prepared.size + 2 * channels) (slot + 2) else final).size
      rw [ite_eq_right covered]
      rfl


/-- The retained heap boundary is formed from the two loaded source counts
and the physically saved inverse base. The inverse word remains above the
saved boundary for dictionary reset; no heap-size instruction is used. -/
def keepCode (width : Nat) : Code width :=
  [.pop 3, .constant 0 (word width 0), .load 0 0,
   .constant 2 (word width 1), .load 2 2, .add 0 0 2, .add 0 0 3,
   .push 0, .push 3, .constant 2 (word width 0), .constant 3 (word width 0)]

@[simp] theorem keepCode_length : (keepCode width).length = 11 := rfl

/-- Eleven fetched steps save the actual dictionary endpoint once, preserving
both source counts, the table base, and the caller's output and heap. -/
theorem keep_execution (program : Program width 4) (heap : Array (Word width))
    (base tableBase inverseBase channels nodes : Nat) (stack output : List (Word width))
    (headerSize : 1 < heap.size)
    (channelsCell : heap[0]? = some (word width channels))
    (nodesCell : heap[1]? = some (word width nodes))
    (room : inverseBase + (channels + nodes) < 2 ^ width)
    (endpoint : heap.size = inverseBase + (channels + nodes))
    (fits : base + 11 < 2 ^ width) (block : BlockAt program base (keepCode width)) :
    Execution program
      (atState heap base 0 tableBase 0 0 (word width inverseBase :: stack) output)
      (atState heap (base + 11) (inverseBase + (channels + nodes)) tableBase 0 0
        (word width inverseBase :: word width (inverseBase + (channels + nodes)) :: stack) output)
      11 (7 + heap.size + stack.length + output.length) := by
  let keep := inverseBase + (channels + nodes)
  let s0 := atState heap base 0 tableBase 0 0 (word width inverseBase :: stack) output
  let s1 := atState heap (base + 1) 0 tableBase 0 inverseBase stack output
  let s2 := atState heap (base + 2) 0 tableBase 0 inverseBase stack output
  let s3 := atState heap (base + 3) channels tableBase 0 inverseBase stack output
  let s4 := atState heap (base + 4) channels tableBase 1 inverseBase stack output
  let s5 := atState heap (base + 5) channels tableBase nodes inverseBase stack output
  let s6 := atState heap (base + 6) (channels + nodes) tableBase nodes inverseBase stack output
  let s7 := atState heap (base + 7) keep tableBase nodes inverseBase stack output
  let s8 := atState heap (base + 8) keep tableBase nodes inverseBase (word width keep :: stack) output
  let s9 := atState heap (base + 9) keep tableBase nodes inverseBase
    (word width inverseBase :: word width keep :: stack) output
  let s10 := atState heap (base + 10) keep tableBase 0 inverseBase
    (word width inverseBase :: word width keep :: stack) output
  let s11 := atState heap (base + 11) keep tableBase 0 0
    (word width inverseBase :: word width keep :: stack) output
  have zeroWord : (word width 0).val = 0 := by simp [word]
  have oneWord : (word width 1).val = 1 := Nat.mod_eq_of_lt (by omega)
  have channelsWord : (word width channels).val = channels := Nat.mod_eq_of_lt (by omega)
  have nodesWord : (word width nodes).val = nodes := Nat.mod_eq_of_lt (by omega)
  have ambientWord : (word width (channels + nodes)).val = channels + nodes := Nat.mod_eq_of_lt (by omega)
  have inverseWord : (word width inverseBase).val = inverseBase := Nat.mod_eq_of_lt (by omega)
  have actualChannels : heap[0]'(by omega) = word width channels := by
    rw [Array.getElem?_eq_getElem (by omega)] at channelsCell
    exact Option.some.inj channelsCell
  have actualNodes : heap[1]'headerSize = word width nodes := by
    rw [Array.getElem?_eq_getElem headerSize] at nodesCell
    exact Option.some.inj nodesCell
  have t0 : programStep program s0 = some s1 := by
    rw [fetched program s0 base (.pop 3) rfl (by omega)
      (by simpa [keepCode] using block 0 (by simp [keepCode]))]
    change some (({ s0.advance with stack := stack }).put 3 (word width inverseBase)) = some s1
    rw [advance_at _ _ _ _ _ _ _ _ (by omega)]
    change some ((atState heap (base + 1) 0 tableBase 0 0 stack output).put 3 (word width inverseBase)) = some s1
    rw [put3_at]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.constant 0 (word width 0)) rfl (by omega)
      (by simpa [keepCode] using block 1 (by simp [keepCode]))]
    change some (s1.advance.put 0 (word width 0)) = some s2
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (base + 2) (.load 0 0) rfl (by omega)
      (by simpa [keepCode] using block 2 (by simp [keepCode]))]
    change (if h : (word width 0).val < heap.size then
      some (s2.advance.put 0 heap[(word width 0).val]) else none) = some s3
    rw [zeroWord, dite_eq_left (by omega), actualChannels,
      advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have first : Execution program s0 s3 3 (6 + heap.size + stack.length + output.length) := by
    convert Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl s3))) using 1 <;>
      simp only [s0, s1, s2, s3, atState, State.liveWords, List.length_cons] <;> omega
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (base + 3) (.constant 2 (word width 1)) rfl (by omega)
      (by simpa [keepCode] using block 3 (by simp [keepCode]))]
    change some (s3.advance.put 2 (word width 1)) = some s4
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put2_at]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (base + 4) (.load 2 2) rfl (by omega)
      (by simpa [keepCode] using block 4 (by simp [keepCode]))]
    change (if h : (word width 1).val < heap.size then
      some (s4.advance.put 2 heap[(word width 1).val]) else none) = some s5
    rw [oneWord, dite_eq_left headerSize, actualNodes,
      advance_at _ _ _ _ _ _ _ _ (by omega), put2_at]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (base + 5) (.add 0 0 2) rfl (by omega)
      (by simpa [keepCode] using block 5 (by simp [keepCode]))]
    change some (s5.advance.put 0 (word width ((word width channels).val + (word width nodes).val))) = some s6
    rw [channelsWord, nodesWord, advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have t6 : programStep program s6 = some s7 := by
    rw [fetched program s6 (base + 6) (.add 0 0 3) rfl (by omega)
      (by simpa [keepCode] using block 6 (by simp [keepCode]))]
    change some (s6.advance.put 0 (word width ((word width (channels + nodes)).val + (word width inverseBase).val))) = some s7
    rw [ambientWord, inverseWord, Nat.add_comm (channels + nodes) inverseBase,
      advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have middle : Execution program s3 s7 4 (5 + heap.size + stack.length + output.length) := by
    convert Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.refl s7)))) using 1 <;>
      simp only [s3, s4, s5, s6, s7, atState, State.liveWords, Nat.max_self] <;> omega
  have t7 : programStep program s7 = some s8 := by
    rw [fetched program s7 (base + 7) (.push 0) rfl (by omega)
      (by simpa [keepCode] using block 7 (by simp [keepCode]))]
    change some { s7.advance with stack := word width keep :: stack } = some s8
    rw [advance_at _ _ _ _ _ _ _ _ (by omega)]
    rfl
  have t8 : programStep program s8 = some s9 := by
    rw [fetched program s8 (base + 8) (.push 3) rfl (by omega)
      (by simpa [keepCode] using block 8 (by simp [keepCode]))]
    change some { s8.advance with stack := word width inverseBase :: word width keep :: stack } = some s9
    rw [advance_at _ _ _ _ _ _ _ _ (by omega)]
    rfl
  have t9 : programStep program s9 = some s10 := by
    rw [fetched program s9 (base + 9) (.constant 2 (word width 0)) rfl (by omega)
      (by simpa [keepCode] using block 9 (by simp [keepCode]))]
    change some (s9.advance.put 2 (word width 0)) = some s10
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put2_at]
  have t10 : programStep program s10 = some s11 := by
    rw [fetched program s10 (base + 10) (.constant 3 (word width 0)) rfl (by omega)
      (by simpa [keepCode] using block 10 (by simp [keepCode]))]
    change some (s10.advance.put 3 (word width 0)) = some s11
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have last : Execution program s7 s11 4 (7 + heap.size + stack.length + output.length) := by
    convert Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.cons t10 (Execution.refl s11)))) using 1 <;>
      simp only [s7, s8, s9, s10, s11, atState, State.liveWords, List.length_cons] <;> omega
  convert (first.append middle).append last using 1 <;>
    (try simp only [s0, s11, keep]) <;> omega


/-- Fixed runtime formation of the scratch count and allocation registers. -/
def scratchCountCode (width : Nat) : Array (Instruction width 8) :=
  #[.copy 4 2, .copy 3 1, .copy 7 1, .add 1 2 2, .add 1 1 1,
    .add 1 1 4, .constant 0 (word width 4), .add 1 1 0,
    .constant 2 (word width 0), .constant 5 (word width 1),
    .constant 6 (word width (2 ^ width - 1))]

@[simp] theorem scratchCountCode_size : (scratchCountCode width).size = 11 := rfl

def scratchCountState (state : State width 8) (n : Nat) : State width 8 :=
  let s1 := state.advance.put 4 (word width (n))
  let s2 := s1.advance.put 3 (word width (state.heap.size))
  let s3 := s2.advance.put 7 (word width (state.heap.size))
  let s4 := s3.advance.put 1 (word width (2 * n))
  let s5 := s4.advance.put 1 (word width (4 * n))
  let s6 := s5.advance.put 1 (word width (5 * n))
  let s7 := s6.advance.put 0 (word width (4))
  let s8 := s7.advance.put 1 (word width (5 * n + 4))
  let s9 := s8.advance.put 2 (word width (0))
  let s10 := s9.advance.put 5 (word width (1))
  let s11 := s10.advance.put 6 (word width (2 ^ width - 1))
  s11

private theorem fetched8 (program : Program width 8) (state : State width 8)
    (cursor : Nat) (instruction : Instruction width 8)
    (pc : state.pc = word width cursor) (fits : cursor < 2 ^ width)
    (entry : program[cursor]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [pc, show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits, entry]
  rfl

private theorem advance8_pc (state : State width 8) (cursor : Nat)
    (pc : state.pc = word width cursor) (fits : cursor < 2 ^ width) :
    state.advance.pc = word width (cursor + 1) := by
  simp only [State.advance, pc]
  rw [show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits]

/-- The allocation counter is computed from the executed caller's count;
the allocation base is copied from its physical source endpoint register. -/
theorem scratch_count_execution (program : Program width 8) (state : State width 8)
    (entry n : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (localCount : state.reg 2 = word width n)
    (pointer : state.reg 1 = word width state.heap.size)
    (capacity : entry + 11 < 2 ^ width)
    (room : state.heap.size + 5 * n + 4 < 2 ^ width)
    (present : ∀ phase : Fin 11, program[entry + phase.val]? = (scratchCountCode width)[phase.val]?) :
    let final := scratchCountState state n
    Execution program state final 11 state.liveWords ∧
      final.reg 1 = word width (5 * n + 4) ∧ final.reg 2 = word width 0 ∧
      final.reg 3 = word width state.heap.size ∧ final.reg 4 = word width n ∧
      final.reg 5 = word width 1 ∧ final.reg 6 = word width (2 ^ width - 1) ∧
      final.reg 7 = word width state.heap.size ∧ final.heap = state.heap ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 11) ∧ final.halted = false := by
  let s1 := state.advance.put 4 (word width (n))
  let s2 := s1.advance.put 3 (word width (state.heap.size))
  let s3 := s2.advance.put 7 (word width (state.heap.size))
  let s4 := s3.advance.put 1 (word width (2 * n))
  let s5 := s4.advance.put 1 (word width (4 * n))
  let s6 := s5.advance.put 1 (word width (5 * n))
  let s7 := s6.advance.put 0 (word width (4))
  let s8 := s7.advance.put 1 (word width (5 * n + 4))
  let s9 := s8.advance.put 2 (word width (0))
  let s10 := s9.advance.put 5 (word width (1))
  let s11 := s10.advance.put 6 (word width (2 ^ width - 1))
  have p1 : s1.pc = word width (entry + 1) := by
    simpa only [s1, State.put, Nat.add_assoc] using advance8_pc state entry position (by omega)
  have p2 : s2.pc = word width (entry + 2) := by
    simpa only [s2, State.put, Nat.add_assoc] using advance8_pc s1 (entry + 1) p1 (by omega)
  have p3 : s3.pc = word width (entry + 3) := by
    simpa only [s3, State.put, Nat.add_assoc] using advance8_pc s2 (entry + 2) p2 (by omega)
  have p4 : s4.pc = word width (entry + 4) := by
    simpa only [s4, State.put, Nat.add_assoc] using advance8_pc s3 (entry + 3) p3 (by omega)
  have p5 : s5.pc = word width (entry + 5) := by
    simpa only [s5, State.put, Nat.add_assoc] using advance8_pc s4 (entry + 4) p4 (by omega)
  have p6 : s6.pc = word width (entry + 6) := by
    simpa only [s6, State.put, Nat.add_assoc] using advance8_pc s5 (entry + 5) p5 (by omega)
  have p7 : s7.pc = word width (entry + 7) := by
    simpa only [s7, State.put, Nat.add_assoc] using advance8_pc s6 (entry + 6) p6 (by omega)
  have p8 : s8.pc = word width (entry + 8) := by
    simpa only [s8, State.put, Nat.add_assoc] using advance8_pc s7 (entry + 7) p7 (by omega)
  have p9 : s9.pc = word width (entry + 9) := by
    simpa only [s9, State.put, Nat.add_assoc] using advance8_pc s8 (entry + 8) p8 (by omega)
  have p10 : s10.pc = word width (entry + 10) := by
    simpa only [s10, State.put, Nat.add_assoc] using advance8_pc s9 (entry + 9) p9 (by omega)
  have p11 : s11.pc = word width (entry + 11) := by
    simpa only [s11, State.put, Nat.add_assoc] using advance8_pc s10 (entry + 10) p10 (by omega)
  have wordValue (value : Nat) (bound : value < 2 ^ width) : (word width value).val = value := Nat.mod_eq_of_lt bound
  have t0 : programStep program state = some s1 := by
    rw [fetched8 program state entry (.copy 4 2) position (by omega)
      (by simpa [scratchCountCode] using present ⟨0, by decide⟩)]
    change (if state.halted then none else some (state.advance.put 4 (state.reg 2))) = some s1
    have active : state.halted = false := by simp only [State.advance, State.put, running]
    have value : state.reg 2 = word width (n) := by simp [State.advance, State.put, localCount, pointer]
    rw [active, value]
    rfl
  have t1 : programStep program s1 = some s2 := by
    rw [fetched8 program s1 (entry + 1) (.copy 3 1) p1 (by omega)
      (by simpa [scratchCountCode] using present ⟨1, by decide⟩)]
    change (if s1.halted then none else some (s1.advance.put 3 (s1.reg 1))) = some s2
    have active : s1.halted = false := by simp only [s1, State.advance, State.put, running]
    have value : s1.reg 1 = word width (state.heap.size) := by simp [s1, State.advance, State.put, localCount, pointer]
    rw [active, value]
    rfl
  have t2 : programStep program s2 = some s3 := by
    rw [fetched8 program s2 (entry + 2) (.copy 7 1) p2 (by omega)
      (by simpa [scratchCountCode] using present ⟨2, by decide⟩)]
    change (if s2.halted then none else some (s2.advance.put 7 (s2.reg 1))) = some s3
    have active : s2.halted = false := by simp only [s2, s1, State.advance, State.put, running]
    have value : s2.reg 1 = word width (state.heap.size) := by simp [s2, s1, State.advance, State.put, localCount, pointer]
    rw [active, value]
    rfl
  have t3 : programStep program s3 = some s4 := by
    rw [fetched8 program s3 (entry + 3) (.add 1 2 2) p3 (by omega)
      (by simpa [scratchCountCode] using present ⟨3, by decide⟩)]
    change (if s3.halted then none else some (s3.advance.put 1
      (word width ((s3.reg 2).val + (s3.reg 2).val)))) = some s4
    have active : s3.halted = false := by simp only [s3, s2, s1, State.advance, State.put, running]
    have leftValue : s3.reg 2 = word width (n) := by simp [s3, s2, s1, State.advance, State.put, localCount, pointer]
    have rightValue : s3.reg 2 = word width (n) := by simp [s3, s2, s1, State.advance, State.put, localCount, pointer]
    rw [active, leftValue, wordValue (n) (by omega),
      show (n) + (n) = 2 * n from by omega]
    rfl
  have t4 : programStep program s4 = some s5 := by
    rw [fetched8 program s4 (entry + 4) (.add 1 1 1) p4 (by omega)
      (by simpa [scratchCountCode] using present ⟨4, by decide⟩)]
    change (if s4.halted then none else some (s4.advance.put 1
      (word width ((s4.reg 1).val + (s4.reg 1).val)))) = some s5
    have active : s4.halted = false := by simp only [s4, s3, s2, s1, State.advance, State.put, running]
    have leftValue : s4.reg 1 = word width (2 * n) := by simp [s4, s3, s2, s1, State.advance, State.put, localCount, pointer]
    have rightValue : s4.reg 1 = word width (2 * n) := by simp [s4, s3, s2, s1, State.advance, State.put, localCount, pointer]
    rw [active, leftValue, wordValue (2 * n) (by omega),
      show (2 * n) + (2 * n) = 4 * n from by omega]
    rfl
  have t5 : programStep program s5 = some s6 := by
    rw [fetched8 program s5 (entry + 5) (.add 1 1 4) p5 (by omega)
      (by simpa [scratchCountCode] using present ⟨5, by decide⟩)]
    change (if s5.halted then none else some (s5.advance.put 1
      (word width ((s5.reg 1).val + (s5.reg 4).val)))) = some s6
    have active : s5.halted = false := by simp only [s5, s4, s3, s2, s1, State.advance, State.put, running]
    have leftValue : s5.reg 1 = word width (4 * n) := by simp [s5, s4, s3, s2, s1, State.advance, State.put, localCount, pointer]
    have rightValue : s5.reg 4 = word width (n) := by simp [s5, s4, s3, s2, s1, State.advance, State.put, localCount, pointer]
    rw [active, leftValue, rightValue, wordValue (4 * n) (by omega), wordValue (n) (by omega),
      show (4 * n) + (n) = 5 * n from by omega]
    rfl
  have t6 : programStep program s6 = some s7 := by
    rw [fetched8 program s6 (entry + 6) (.constant 0 (word width (4))) p6 (by omega)
      (by simpa [scratchCountCode] using present ⟨6, by decide⟩)]
    change (if s6.halted then none else some (s6.advance.put 0 (word width (4)))) = some s7
    have active : s6.halted = false := by simp only [s6, s5, s4, s3, s2, s1, State.advance, State.put, running]
    rw [active]
    rfl
  have t7 : programStep program s7 = some s8 := by
    rw [fetched8 program s7 (entry + 7) (.add 1 1 0) p7 (by omega)
      (by simpa [scratchCountCode] using present ⟨7, by decide⟩)]
    change (if s7.halted then none else some (s7.advance.put 1
      (word width ((s7.reg 1).val + (s7.reg 0).val)))) = some s8
    have active : s7.halted = false := by simp only [s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running]
    have leftValue : s7.reg 1 = word width (5 * n) := by simp [s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, localCount, pointer]
    have rightValue : s7.reg 0 = word width (4) := by simp [s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, localCount, pointer]
    rw [active, leftValue, rightValue, wordValue (5 * n) (by omega), wordValue (4) (by omega),
      show (5 * n) + (4) = 5 * n + 4 from by omega]
    rfl
  have t8 : programStep program s8 = some s9 := by
    rw [fetched8 program s8 (entry + 8) (.constant 2 (word width (0))) p8 (by omega)
      (by simpa [scratchCountCode] using present ⟨8, by decide⟩)]
    change (if s8.halted then none else some (s8.advance.put 2 (word width (0)))) = some s9
    have active : s8.halted = false := by simp only [s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running]
    rw [active]
    rfl
  have t9 : programStep program s9 = some s10 := by
    rw [fetched8 program s9 (entry + 9) (.constant 5 (word width (1))) p9 (by omega)
      (by simpa [scratchCountCode] using present ⟨9, by decide⟩)]
    change (if s9.halted then none else some (s9.advance.put 5 (word width (1)))) = some s10
    have active : s9.halted = false := by simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running]
    rw [active]
    rfl
  have t10 : programStep program s10 = some s11 := by
    rw [fetched8 program s10 (entry + 10) (.constant 6 (word width (2 ^ width - 1))) p10 (by omega)
      (by simpa [scratchCountCode] using present ⟨10, by decide⟩)]
    change (if s10.halted then none else some (s10.advance.put 6 (word width (2 ^ width - 1)))) = some s11
    have active : s10.halted = false := by simp only [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running]
    rw [active]
    rfl
  have live1 : s1.liveWords = state.liveWords := rfl
  have live2 : s2.liveWords = state.liveWords := rfl
  have live3 : s3.liveWords = state.liveWords := rfl
  have live4 : s4.liveWords = state.liveWords := rfl
  have live5 : s5.liveWords = state.liveWords := rfl
  have live6 : s6.liveWords = state.liveWords := rfl
  have live7 : s7.liveWords = state.liveWords := rfl
  have live8 : s8.liveWords = state.liveWords := rfl
  have live9 : s9.liveWords = state.liveWords := rfl
  have live10 : s10.liveWords = state.liveWords := rfl
  have live11 : s11.liveWords = state.liveWords := rfl
  have chunk0 : Execution program state s3 3 state.liveWords := by
    convert Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl s3))) using 1 <;> (try simp only [Nat.max_self, live1, live2, live3, Nat.max_self])
  have chunk1 : Execution program s3 s6 3 state.liveWords := by
    convert Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.refl s6))) using 1 <;> (try simp only [live3, live4, live5, live6, Nat.max_self])
  have chunk2 : Execution program s6 s9 3 state.liveWords := by
    convert Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.refl s9))) using 1 <;> (try simp only [live6, live7, live8, live9, Nat.max_self])
  have chunk3 : Execution program s9 s11 2 state.liveWords := by
    convert Execution.cons t9 (Execution.cons t10 (Execution.refl s11)) using 1 <;> (try simp only [live9, live10, live11, Nat.max_self])
  have trace : Execution program state s11 11 state.liveWords := by
    convert ((chunk0.append chunk1).append chunk2).append chunk3 using 1 <;>
      simp only [Nat.max_self]
  refine ⟨trace, ?_⟩
  simp only [scratchCountState, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.put, State.advance]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | rfl | trivial | exact p11 | exact running


/-- Runtime count formation and the shared tracked allocation loop reserve the
complete normalizer scratch. Every old heap cell and the saved caller stack
survive; the heap-end register is the result of the executed allocations. -/
theorem scratch_allocate_execution (program : Program width 8) (state : State width 8)
    (entry n : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (localCount : state.reg 2 = word width n)
    (pointer : state.reg 1 = word width state.heap.size)
    (capacity : entry + 16 < 2 ^ width)
    (room : state.heap.size + 5 * n + 4 < 2 ^ width)
    (countAt : ∀ phase : Fin 11, program[entry + phase.val]? = (scratchCountCode width)[phase.val]?)
    (allocateAt : Controller.Horn.TrackedAllocate.CodeAt program (entry + 11)) :
    ∃ final : State width 8,
      Execution program state final (25 * n + 32) (state.liveWords + 5 * n + 4) ∧
      final.heap = state.heap ++ Array.replicate (5 * n + 4) (word width 0) ∧
      final.reg 2 = word width 0 ∧ final.reg 3 = word width state.heap.size ∧
      final.reg 4 = word width n ∧ final.reg 5 = word width 1 ∧
      final.reg 6 = word width (2 ^ width - 1) ∧
      final.reg 7 = word width (state.heap.size + 5 * n + 4) ∧
      final.pc = word width (entry + 16) ∧ final.halted = false ∧
      final.stack = state.stack ∧ final.output = state.output := by
  let counted := scratchCountState state n
  obtain ⟨countTrace, counter, zero, baseWord, localWord, one, mask, cursor,
    heapEq, stackEq, outputEq, positionEq, runningEq⟩ :=
    scratch_count_execution program state entry n position running localCount pointer (by omega) room countAt
  let allocated := Controller.Horn.TrackedAllocate.configuration counted
    (state.heap ++ Array.replicate (5 * n + 4) (word width 0)) 0 (entry + 16)
  have countedHeap : counted.heap = state.heap := heapEq
  have countedStack : counted.stack = state.stack := stackEq
  have countedOutput : counted.output = state.output := outputEq
  have countedLive : counted.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [countedHeap, countedStack, countedOutput]
  have allocatedTrace : Execution program counted allocated (5 * (5 * n + 4) + 1)
      (state.liveWords + 5 * n + 4) := by
    have actual := Controller.Horn.TrackedAllocate.execution_from_state program (entry + 11)
      allocateAt counted (5 * n + 4) counter positionEq runningEq
      (by rw [countedHeap]; exact cursor) zero one mask (by omega)
      (by rw [countedHeap]; exact room)
    rw [countedHeap, countedLive] at actual
    simpa only [allocated, show entry + 11 + 5 = entry + 16 by omega,
      Nat.add_assoc] using actual
  have joined : Execution program state allocated (25 * n + 32)
      (state.liveWords + 5 * n + 4) := by
    convert countTrace.append allocatedTrace using 1 <;> omega
  refine ⟨allocated, joined, rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · simpa [allocated, Controller.Horn.TrackedAllocate.configuration] using zero
  · simpa [allocated, Controller.Horn.TrackedAllocate.configuration] using baseWord
  · simpa [allocated, Controller.Horn.TrackedAllocate.configuration] using localWord
  · simpa [allocated, Controller.Horn.TrackedAllocate.configuration] using one
  · simpa [allocated, Controller.Horn.TrackedAllocate.configuration] using mask
  · simp [allocated, Controller.Horn.TrackedAllocate.configuration, Array.size_append,
      Array.size_replicate, Nat.add_assoc]
  · exact stackEq
  · exact outputEq


/-- Runtime cursor stores use the saved scratch base and local count. -/
def scratchHeaderCode (width : Nat) : Array (Instruction width 8) :=
  #[.add 0 4 4, .add 0 0 3, .add 1 0 4, .constant 6 (word width 4),
    .add 1 1 6, .store 0 1, .add 0 0 5, .add 1 1 4, .store 0 1,
    .add 0 0 5, .add 1 1 4, .store 0 1, .add 0 0 5, .store 0 2,
    .constant 6 (word width (2 ^ width - 1))]

@[simp] theorem scratchHeaderCode_size : (scratchHeaderCode width).size = 15 := rfl

def scratchHeaderHeap (heap : Array (Word width)) (base n : Nat) : Array (Word width) :=
  let first := heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
  let second := first.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
  let third := second.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
  third.setIfInBounds (base + 2 * n + 3) (word width 0)

@[simp] theorem scratchHeaderHeap_size (heap : Array (Word width)) (base n : Nat) :
    (scratchHeaderHeap heap base n).size = heap.size := by
  simp only [scratchHeaderHeap, Array.size_setIfInBounds]

def scratchHeaderConfiguration (state : State width 8) (heap : Array (Word width))
    (cursor : Nat) (value0 value1 value6 : Word width) : State width 8 :=
  { state with
    heap := heap
    pc := word width cursor
    reg := fun register => if register = 0 then value0 else
      if register = 1 then value1 else if register = 6 then value6 else state.reg register }

def scratchHeaderState (state : State width 8) (base n : Nat) : State width 8 :=
  scratchHeaderConfiguration state (scratchHeaderHeap state.heap base n) (state.pc.val + 15)
    (word width (base + 2 * n + 3)) (word width (base + 5 * n + 4)) (word width (2 ^ width - 1))

/- Each fixed fetched transition has its own declaration. The public
header trace only composes these checked endpoints; normalizing one transition
never unfolds the other fourteen configurations. -/

private theorem scratch_header_transition_0 (program : Program width 8) (state : State width 8)
    (entry base n : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (baseWord : state.reg 3 = word width base)
    (countWord : state.reg 4 = word width n) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = word width 1) (sizeEq : state.heap.size = base + 5 * n + 4)
    (room : state.heap.size < 2 ^ width) (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? = (scratchHeaderCode width)[phase.val]?) :
    let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
    let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
    let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
    let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
    let s1 := scratchHeaderConfiguration state state.heap (entry + 1) (word width (2 * n)) (state.reg 1) (state.reg 6)
    programStep program state = some s1 := by
  let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
  let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
  let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
  let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
  have h1Size : h1.size = state.heap.size := by simp only [h1, Array.size_setIfInBounds]
  have h2Size : h2.size = state.heap.size := by simp only [h2, Array.size_setIfInBounds, h1Size]
  have h3Size : h3.size = state.heap.size := by simp only [h3, Array.size_setIfInBounds, h2Size]
  have h4Size : h4.size = state.heap.size := by simp only [h4, Array.size_setIfInBounds, h3Size]
  have bound0 : base + 2 * n < state.heap.size := by rw [sizeEq]; omega
  have bound1 : base + 2 * n + 1 < state.heap.size := by rw [sizeEq]; omega
  have bound2 : base + 2 * n + 2 < state.heap.size := by rw [sizeEq]; omega
  have bound3 : base + 2 * n + 3 < state.heap.size := by rw [sizeEq]; omega
  have add0 : n + n = 2 * n := by omega
  have addressFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have scalarRoom : base + 5 * n + 4 < 2 ^ width := by
    rw [← sizeEq]
    exact room
  have pcValue : state.pc.val = entry := by rw [position]; exact Nat.mod_eq_of_lt (addressFits 0 (by decide))
  let s1 := scratchHeaderConfiguration state state.heap (entry + 1) (word width (2 * n)) (state.reg 1) (state.reg 6)
  have w0 : (word width (n)).val = n := Nat.mod_eq_of_lt (by omega)
  have pc0 : (word width (entry + 0)).val = entry + 0 := Nat.mod_eq_of_lt (addressFits 0 (by decide))
  have nextPC : entry + 0 + 1 = entry + 1 := by omega
  change programStep program state = some s1
  rw [fetched8 program state (entry + 0) (.add 0 4 4)
    (by simpa only [Nat.add_zero] using position) (addressFits 0 (by decide))
    (by simpa [scratchHeaderCode] using present ⟨0, by decide⟩)]
  simp [s1, scratchHeaderConfiguration, step, State.advance, State.put, running, baseWord, countWord, zero, one, pcValue, w0, pc0, add0, nextPC]
  all_goals first
    | rfl
    | (congr 1; funext register; fin_cases register <;> rfl)

private theorem scratch_header_transition_1 (program : Program width 8) (state : State width 8)
    (entry base n : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (baseWord : state.reg 3 = word width base)
    (countWord : state.reg 4 = word width n) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = word width 1) (sizeEq : state.heap.size = base + 5 * n + 4)
    (room : state.heap.size < 2 ^ width) (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? = (scratchHeaderCode width)[phase.val]?) :
    let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
    let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
    let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
    let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
    let s1 := scratchHeaderConfiguration state state.heap (entry + 1) (word width (2 * n)) (state.reg 1) (state.reg 6)
    let s2 := scratchHeaderConfiguration state state.heap (entry + 2) (word width (base + 2 * n)) (state.reg 1) (state.reg 6)
    programStep program s1 = some s2 := by
  let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
  let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
  let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
  let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
  have h1Size : h1.size = state.heap.size := by simp only [h1, Array.size_setIfInBounds]
  have h2Size : h2.size = state.heap.size := by simp only [h2, Array.size_setIfInBounds, h1Size]
  have h3Size : h3.size = state.heap.size := by simp only [h3, Array.size_setIfInBounds, h2Size]
  have h4Size : h4.size = state.heap.size := by simp only [h4, Array.size_setIfInBounds, h3Size]
  have bound0 : base + 2 * n < state.heap.size := by rw [sizeEq]; omega
  have bound1 : base + 2 * n + 1 < state.heap.size := by rw [sizeEq]; omega
  have bound2 : base + 2 * n + 2 < state.heap.size := by rw [sizeEq]; omega
  have bound3 : base + 2 * n + 3 < state.heap.size := by rw [sizeEq]; omega
  have add1 : 2 * n + base = base + 2 * n := by omega
  have addressFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have scalarRoom : base + 5 * n + 4 < 2 ^ width := by
    rw [← sizeEq]
    exact room
  let s1 := scratchHeaderConfiguration state state.heap (entry + 1) (word width (2 * n)) (state.reg 1) (state.reg 6)
  let s2 := scratchHeaderConfiguration state state.heap (entry + 2) (word width (base + 2 * n)) (state.reg 1) (state.reg 6)
  have w1 : (word width (base)).val = base := Nat.mod_eq_of_lt (by omega)
  have w2 : (word width (2 * n)).val = 2 * n := Nat.mod_eq_of_lt (by omega)
  have pc1 : (word width (entry + 1)).val = entry + 1 := Nat.mod_eq_of_lt (addressFits 1 (by decide))
  have nextPC : entry + 1 + 1 = entry + 2 := by omega
  change programStep program s1 = some s2
  rw [fetched8 program s1 (entry + 1) (.add 0 0 3)
    (by rfl) (addressFits 1 (by decide))
    (by simpa [scratchHeaderCode] using present ⟨1, by decide⟩)]
  simp [s2, s1, scratchHeaderConfiguration, step, State.advance, State.put, running, baseWord, countWord, zero, one, w1, w2, pc1, add1, nextPC]
  all_goals first
    | rfl
    | (congr 1; funext register; fin_cases register <;> rfl)

private theorem scratch_header_transition_2 (program : Program width 8) (state : State width 8)
    (entry base n : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (baseWord : state.reg 3 = word width base)
    (countWord : state.reg 4 = word width n) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = word width 1) (sizeEq : state.heap.size = base + 5 * n + 4)
    (room : state.heap.size < 2 ^ width) (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? = (scratchHeaderCode width)[phase.val]?) :
    let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
    let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
    let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
    let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
    let s2 := scratchHeaderConfiguration state state.heap (entry + 2) (word width (base + 2 * n)) (state.reg 1) (state.reg 6)
    let s3 := scratchHeaderConfiguration state state.heap (entry + 3) (word width (base + 2 * n)) (word width (base + 3 * n)) (state.reg 6)
    programStep program s2 = some s3 := by
  let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
  let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
  let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
  let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
  have h1Size : h1.size = state.heap.size := by simp only [h1, Array.size_setIfInBounds]
  have h2Size : h2.size = state.heap.size := by simp only [h2, Array.size_setIfInBounds, h1Size]
  have h3Size : h3.size = state.heap.size := by simp only [h3, Array.size_setIfInBounds, h2Size]
  have h4Size : h4.size = state.heap.size := by simp only [h4, Array.size_setIfInBounds, h3Size]
  have bound0 : base + 2 * n < state.heap.size := by rw [sizeEq]; omega
  have bound1 : base + 2 * n + 1 < state.heap.size := by rw [sizeEq]; omega
  have bound2 : base + 2 * n + 2 < state.heap.size := by rw [sizeEq]; omega
  have bound3 : base + 2 * n + 3 < state.heap.size := by rw [sizeEq]; omega
  have add2 : base + 2 * n + n = base + 3 * n := by omega
  have addressFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have scalarRoom : base + 5 * n + 4 < 2 ^ width := by
    rw [← sizeEq]
    exact room
  let s2 := scratchHeaderConfiguration state state.heap (entry + 2) (word width (base + 2 * n)) (state.reg 1) (state.reg 6)
  let s3 := scratchHeaderConfiguration state state.heap (entry + 3) (word width (base + 2 * n)) (word width (base + 3 * n)) (state.reg 6)
  have w0 : (word width (n)).val = n := Nat.mod_eq_of_lt (by omega)
  have w3 : (word width (base + 2 * n)).val = base + 2 * n := Nat.mod_eq_of_lt (by omega)
  have pc2 : (word width (entry + 2)).val = entry + 2 := Nat.mod_eq_of_lt (addressFits 2 (by decide))
  have nextPC : entry + 2 + 1 = entry + 3 := by omega
  change programStep program s2 = some s3
  rw [fetched8 program s2 (entry + 2) (.add 1 0 4)
    (by rfl) (addressFits 2 (by decide))
    (by simpa [scratchHeaderCode] using present ⟨2, by decide⟩)]
  simp [s3, s2, scratchHeaderConfiguration, step, State.advance, State.put, running, baseWord, countWord, zero, one, w0, w3, pc2, add2, nextPC]
  all_goals first
    | rfl
    | (congr 1; funext register; fin_cases register <;> rfl)

private theorem scratch_header_transition_3 (program : Program width 8) (state : State width 8)
    (entry base n : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (baseWord : state.reg 3 = word width base)
    (countWord : state.reg 4 = word width n) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = word width 1) (sizeEq : state.heap.size = base + 5 * n + 4)
    (room : state.heap.size < 2 ^ width) (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? = (scratchHeaderCode width)[phase.val]?) :
    let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
    let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
    let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
    let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
    let s3 := scratchHeaderConfiguration state state.heap (entry + 3) (word width (base + 2 * n)) (word width (base + 3 * n)) (state.reg 6)
    let s4 := scratchHeaderConfiguration state state.heap (entry + 4) (word width (base + 2 * n)) (word width (base + 3 * n)) (word width 4)
    programStep program s3 = some s4 := by
  let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
  let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
  let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
  let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
  have h1Size : h1.size = state.heap.size := by simp only [h1, Array.size_setIfInBounds]
  have h2Size : h2.size = state.heap.size := by simp only [h2, Array.size_setIfInBounds, h1Size]
  have h3Size : h3.size = state.heap.size := by simp only [h3, Array.size_setIfInBounds, h2Size]
  have h4Size : h4.size = state.heap.size := by simp only [h4, Array.size_setIfInBounds, h3Size]
  have bound0 : base + 2 * n < state.heap.size := by rw [sizeEq]; omega
  have bound1 : base + 2 * n + 1 < state.heap.size := by rw [sizeEq]; omega
  have bound2 : base + 2 * n + 2 < state.heap.size := by rw [sizeEq]; omega
  have bound3 : base + 2 * n + 3 < state.heap.size := by rw [sizeEq]; omega
  have addressFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have scalarRoom : base + 5 * n + 4 < 2 ^ width := by
    rw [← sizeEq]
    exact room
  let s3 := scratchHeaderConfiguration state state.heap (entry + 3) (word width (base + 2 * n)) (word width (base + 3 * n)) (state.reg 6)
  let s4 := scratchHeaderConfiguration state state.heap (entry + 4) (word width (base + 2 * n)) (word width (base + 3 * n)) (word width 4)
  have pc3 : (word width (entry + 3)).val = entry + 3 := Nat.mod_eq_of_lt (addressFits 3 (by decide))
  have nextPC : entry + 3 + 1 = entry + 4 := by omega
  change programStep program s3 = some s4
  rw [fetched8 program s3 (entry + 3) (.constant 6 (word width 4))
    (by rfl) (addressFits 3 (by decide))
    (by simpa [scratchHeaderCode] using present ⟨3, by decide⟩)]
  simp [s4, s3, scratchHeaderConfiguration, step, State.advance, State.put, running, baseWord, countWord, zero, one, pc3, nextPC]
  all_goals first
    | rfl
    | (congr 1; funext register; fin_cases register <;> rfl)

private theorem scratch_header_transition_4 (program : Program width 8) (state : State width 8)
    (entry base n : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (baseWord : state.reg 3 = word width base)
    (countWord : state.reg 4 = word width n) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = word width 1) (sizeEq : state.heap.size = base + 5 * n + 4)
    (room : state.heap.size < 2 ^ width) (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? = (scratchHeaderCode width)[phase.val]?) :
    let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
    let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
    let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
    let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
    let s4 := scratchHeaderConfiguration state state.heap (entry + 4) (word width (base + 2 * n)) (word width (base + 3 * n)) (word width 4)
    let s5 := scratchHeaderConfiguration state state.heap (entry + 5) (word width (base + 2 * n)) (word width (base + 3 * n + 4)) (word width 4)
    programStep program s4 = some s5 := by
  let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
  let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
  let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
  let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
  have h1Size : h1.size = state.heap.size := by simp only [h1, Array.size_setIfInBounds]
  have h2Size : h2.size = state.heap.size := by simp only [h2, Array.size_setIfInBounds, h1Size]
  have h3Size : h3.size = state.heap.size := by simp only [h3, Array.size_setIfInBounds, h2Size]
  have h4Size : h4.size = state.heap.size := by simp only [h4, Array.size_setIfInBounds, h3Size]
  have bound0 : base + 2 * n < state.heap.size := by rw [sizeEq]; omega
  have bound1 : base + 2 * n + 1 < state.heap.size := by rw [sizeEq]; omega
  have bound2 : base + 2 * n + 2 < state.heap.size := by rw [sizeEq]; omega
  have bound3 : base + 2 * n + 3 < state.heap.size := by rw [sizeEq]; omega
  have addressFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have scalarRoom : base + 5 * n + 4 < 2 ^ width := by
    rw [← sizeEq]
    exact room
  let s4 := scratchHeaderConfiguration state state.heap (entry + 4) (word width (base + 2 * n)) (word width (base + 3 * n)) (word width 4)
  let s5 := scratchHeaderConfiguration state state.heap (entry + 5) (word width (base + 2 * n)) (word width (base + 3 * n + 4)) (word width 4)
  have w7 : (word width (base + 3 * n)).val = base + 3 * n := Nat.mod_eq_of_lt (by omega)
  have w13 : (word width (4)).val = 4 := Nat.mod_eq_of_lt (by omega)
  have pc4 : (word width (entry + 4)).val = entry + 4 := Nat.mod_eq_of_lt (addressFits 4 (by decide))
  have nextPC : entry + 4 + 1 = entry + 5 := by omega
  change programStep program s4 = some s5
  rw [fetched8 program s4 (entry + 4) (.add 1 1 6)
    (by rfl) (addressFits 4 (by decide))
    (by simpa [scratchHeaderCode] using present ⟨4, by decide⟩)]
  simp [s5, s4, scratchHeaderConfiguration, step, State.advance, State.put, running, baseWord, countWord, zero, one, w7, w13, pc4, nextPC]
  all_goals first
    | rfl
    | (congr 1; funext register; fin_cases register <;> rfl)

private theorem scratch_header_transition_5 (program : Program width 8) (state : State width 8)
    (entry base n : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (baseWord : state.reg 3 = word width base)
    (countWord : state.reg 4 = word width n) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = word width 1) (sizeEq : state.heap.size = base + 5 * n + 4)
    (room : state.heap.size < 2 ^ width) (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? = (scratchHeaderCode width)[phase.val]?) :
    let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
    let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
    let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
    let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
    let s5 := scratchHeaderConfiguration state state.heap (entry + 5) (word width (base + 2 * n)) (word width (base + 3 * n + 4)) (word width 4)
    let s6 := scratchHeaderConfiguration state h1 (entry + 6) (word width (base + 2 * n)) (word width (base + 3 * n + 4)) (word width 4)
    programStep program s5 = some s6 := by
  let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
  let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
  let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
  let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
  have h1Size : h1.size = state.heap.size := by simp only [h1, Array.size_setIfInBounds]
  have h2Size : h2.size = state.heap.size := by simp only [h2, Array.size_setIfInBounds, h1Size]
  have h3Size : h3.size = state.heap.size := by simp only [h3, Array.size_setIfInBounds, h2Size]
  have h4Size : h4.size = state.heap.size := by simp only [h4, Array.size_setIfInBounds, h3Size]
  have bound0 : base + 2 * n < state.heap.size := by rw [sizeEq]; omega
  have bound1 : base + 2 * n + 1 < state.heap.size := by rw [sizeEq]; omega
  have bound2 : base + 2 * n + 2 < state.heap.size := by rw [sizeEq]; omega
  have bound3 : base + 2 * n + 3 < state.heap.size := by rw [sizeEq]; omega
  have addressFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have scalarRoom : base + 5 * n + 4 < 2 ^ width := by
    rw [← sizeEq]
    exact room
  let s5 := scratchHeaderConfiguration state state.heap (entry + 5) (word width (base + 2 * n)) (word width (base + 3 * n + 4)) (word width 4)
  let s6 := scratchHeaderConfiguration state h1 (entry + 6) (word width (base + 2 * n)) (word width (base + 3 * n + 4)) (word width 4)
  have w3 : (word width (base + 2 * n)).val = base + 2 * n := Nat.mod_eq_of_lt (by omega)
  have pc5 : (word width (entry + 5)).val = entry + 5 := Nat.mod_eq_of_lt (addressFits 5 (by decide))
  have nextPC : entry + 5 + 1 = entry + 6 := by omega
  change programStep program s5 = some s6
  rw [fetched8 program s5 (entry + 5) (.store 0 1)
    (by rfl) (addressFits 5 (by decide))
    (by simpa [scratchHeaderCode] using present ⟨5, by decide⟩)]
  simp [s6, s5, scratchHeaderConfiguration, step, State.advance, State.put, running, baseWord, countWord, zero, one, w3, pc5, h1, Array.setIfInBounds_def, h1Size, h2Size, h3Size, h4Size, bound0, bound1, bound2, bound3, nextPC]
  all_goals first
    | rfl
    | (congr 1; funext register; fin_cases register <;> rfl)

private theorem scratch_header_transition_6 (program : Program width 8) (state : State width 8)
    (entry base n : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (baseWord : state.reg 3 = word width base)
    (countWord : state.reg 4 = word width n) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = word width 1) (sizeEq : state.heap.size = base + 5 * n + 4)
    (room : state.heap.size < 2 ^ width) (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? = (scratchHeaderCode width)[phase.val]?) :
    let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
    let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
    let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
    let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
    let s6 := scratchHeaderConfiguration state h1 (entry + 6) (word width (base + 2 * n)) (word width (base + 3 * n + 4)) (word width 4)
    let s7 := scratchHeaderConfiguration state h1 (entry + 7) (word width (base + 2 * n + 1)) (word width (base + 3 * n + 4)) (word width 4)
    programStep program s6 = some s7 := by
  let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
  let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
  let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
  let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
  have h1Size : h1.size = state.heap.size := by simp only [h1, Array.size_setIfInBounds]
  have h2Size : h2.size = state.heap.size := by simp only [h2, Array.size_setIfInBounds, h1Size]
  have h3Size : h3.size = state.heap.size := by simp only [h3, Array.size_setIfInBounds, h2Size]
  have h4Size : h4.size = state.heap.size := by simp only [h4, Array.size_setIfInBounds, h3Size]
  have bound0 : base + 2 * n < state.heap.size := by rw [sizeEq]; omega
  have bound1 : base + 2 * n + 1 < state.heap.size := by rw [sizeEq]; omega
  have bound2 : base + 2 * n + 2 < state.heap.size := by rw [sizeEq]; omega
  have bound3 : base + 2 * n + 3 < state.heap.size := by rw [sizeEq]; omega
  have addressFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have scalarRoom : base + 5 * n + 4 < 2 ^ width := by
    rw [← sizeEq]
    exact room
  let s6 := scratchHeaderConfiguration state h1 (entry + 6) (word width (base + 2 * n)) (word width (base + 3 * n + 4)) (word width 4)
  let s7 := scratchHeaderConfiguration state h1 (entry + 7) (word width (base + 2 * n + 1)) (word width (base + 3 * n + 4)) (word width 4)
  have w3 : (word width (base + 2 * n)).val = base + 2 * n := Nat.mod_eq_of_lt (by omega)
  have w12 : (word width (1)).val = 1 := Nat.mod_eq_of_lt (by omega)
  have pc6 : (word width (entry + 6)).val = entry + 6 := Nat.mod_eq_of_lt (addressFits 6 (by decide))
  have nextPC : entry + 6 + 1 = entry + 7 := by omega
  change programStep program s6 = some s7
  rw [fetched8 program s6 (entry + 6) (.add 0 0 5)
    (by rfl) (addressFits 6 (by decide))
    (by simpa [scratchHeaderCode] using present ⟨6, by decide⟩)]
  simp [s7, s6, scratchHeaderConfiguration, step, State.advance, State.put, running, baseWord, countWord, zero, one, w3, w12, pc6, nextPC]
  all_goals first
    | rfl
    | (congr 1; funext register; fin_cases register <;> rfl)

private theorem scratch_header_transition_7 (program : Program width 8) (state : State width 8)
    (entry base n : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (baseWord : state.reg 3 = word width base)
    (countWord : state.reg 4 = word width n) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = word width 1) (sizeEq : state.heap.size = base + 5 * n + 4)
    (room : state.heap.size < 2 ^ width) (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? = (scratchHeaderCode width)[phase.val]?) :
    let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
    let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
    let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
    let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
    let s7 := scratchHeaderConfiguration state h1 (entry + 7) (word width (base + 2 * n + 1)) (word width (base + 3 * n + 4)) (word width 4)
    let s8 := scratchHeaderConfiguration state h1 (entry + 8) (word width (base + 2 * n + 1)) (word width (base + 4 * n + 4)) (word width 4)
    programStep program s7 = some s8 := by
  let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
  let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
  let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
  let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
  have h1Size : h1.size = state.heap.size := by simp only [h1, Array.size_setIfInBounds]
  have h2Size : h2.size = state.heap.size := by simp only [h2, Array.size_setIfInBounds, h1Size]
  have h3Size : h3.size = state.heap.size := by simp only [h3, Array.size_setIfInBounds, h2Size]
  have h4Size : h4.size = state.heap.size := by simp only [h4, Array.size_setIfInBounds, h3Size]
  have bound0 : base + 2 * n < state.heap.size := by rw [sizeEq]; omega
  have bound1 : base + 2 * n + 1 < state.heap.size := by rw [sizeEq]; omega
  have bound2 : base + 2 * n + 2 < state.heap.size := by rw [sizeEq]; omega
  have bound3 : base + 2 * n + 3 < state.heap.size := by rw [sizeEq]; omega
  have add7 : base + 3 * n + 4 + n = base + 4 * n + 4 := by omega
  have addressFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have scalarRoom : base + 5 * n + 4 < 2 ^ width := by
    rw [← sizeEq]
    exact room
  let s7 := scratchHeaderConfiguration state h1 (entry + 7) (word width (base + 2 * n + 1)) (word width (base + 3 * n + 4)) (word width 4)
  let s8 := scratchHeaderConfiguration state h1 (entry + 8) (word width (base + 2 * n + 1)) (word width (base + 4 * n + 4)) (word width 4)
  have w0 : (word width (n)).val = n := Nat.mod_eq_of_lt (by omega)
  have w8 : (word width (base + 3 * n + 4)).val = base + 3 * n + 4 := Nat.mod_eq_of_lt (by omega)
  have pc7 : (word width (entry + 7)).val = entry + 7 := Nat.mod_eq_of_lt (addressFits 7 (by decide))
  have nextPC : entry + 7 + 1 = entry + 8 := by omega
  change programStep program s7 = some s8
  rw [fetched8 program s7 (entry + 7) (.add 1 1 4)
    (by rfl) (addressFits 7 (by decide))
    (by simpa [scratchHeaderCode] using present ⟨7, by decide⟩)]
  simp [s8, s7, scratchHeaderConfiguration, step, State.advance, State.put, running, baseWord, countWord, zero, one, w0, w8, pc7, add7, nextPC]
  all_goals first
    | rfl
    | (congr 1; funext register; fin_cases register <;> rfl)

private theorem scratch_header_transition_8 (program : Program width 8) (state : State width 8)
    (entry base n : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (baseWord : state.reg 3 = word width base)
    (countWord : state.reg 4 = word width n) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = word width 1) (sizeEq : state.heap.size = base + 5 * n + 4)
    (room : state.heap.size < 2 ^ width) (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? = (scratchHeaderCode width)[phase.val]?) :
    let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
    let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
    let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
    let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
    let s8 := scratchHeaderConfiguration state h1 (entry + 8) (word width (base + 2 * n + 1)) (word width (base + 4 * n + 4)) (word width 4)
    let s9 := scratchHeaderConfiguration state h2 (entry + 9) (word width (base + 2 * n + 1)) (word width (base + 4 * n + 4)) (word width 4)
    programStep program s8 = some s9 := by
  let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
  let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
  let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
  let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
  have h1Size : h1.size = state.heap.size := by simp only [h1, Array.size_setIfInBounds]
  have h2Size : h2.size = state.heap.size := by simp only [h2, Array.size_setIfInBounds, h1Size]
  have h3Size : h3.size = state.heap.size := by simp only [h3, Array.size_setIfInBounds, h2Size]
  have h4Size : h4.size = state.heap.size := by simp only [h4, Array.size_setIfInBounds, h3Size]
  have bound0 : base + 2 * n < state.heap.size := by rw [sizeEq]; omega
  have bound1 : base + 2 * n + 1 < state.heap.size := by rw [sizeEq]; omega
  have bound2 : base + 2 * n + 2 < state.heap.size := by rw [sizeEq]; omega
  have bound3 : base + 2 * n + 3 < state.heap.size := by rw [sizeEq]; omega
  have addressFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have scalarRoom : base + 5 * n + 4 < 2 ^ width := by
    rw [← sizeEq]
    exact room
  let s8 := scratchHeaderConfiguration state h1 (entry + 8) (word width (base + 2 * n + 1)) (word width (base + 4 * n + 4)) (word width 4)
  let s9 := scratchHeaderConfiguration state h2 (entry + 9) (word width (base + 2 * n + 1)) (word width (base + 4 * n + 4)) (word width 4)
  have w4 : (word width (base + 2 * n + 1)).val = base + 2 * n + 1 := Nat.mod_eq_of_lt (by omega)
  have pc8 : (word width (entry + 8)).val = entry + 8 := Nat.mod_eq_of_lt (addressFits 8 (by decide))
  have nextPC : entry + 8 + 1 = entry + 9 := by omega
  change programStep program s8 = some s9
  rw [fetched8 program s8 (entry + 8) (.store 0 1)
    (by rfl) (addressFits 8 (by decide))
    (by simpa [scratchHeaderCode] using present ⟨8, by decide⟩)]
  simp [s9, s8, scratchHeaderConfiguration, step, State.advance, State.put, running, baseWord, countWord, zero, one, w4, pc8, h2, Array.setIfInBounds_def, h1Size, h2Size, h3Size, h4Size, bound0, bound1, bound2, bound3, nextPC]
  all_goals first
    | rfl
    | (congr 1; funext register; fin_cases register <;> rfl)

private theorem scratch_header_transition_9 (program : Program width 8) (state : State width 8)
    (entry base n : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (baseWord : state.reg 3 = word width base)
    (countWord : state.reg 4 = word width n) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = word width 1) (sizeEq : state.heap.size = base + 5 * n + 4)
    (room : state.heap.size < 2 ^ width) (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? = (scratchHeaderCode width)[phase.val]?) :
    let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
    let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
    let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
    let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
    let s9 := scratchHeaderConfiguration state h2 (entry + 9) (word width (base + 2 * n + 1)) (word width (base + 4 * n + 4)) (word width 4)
    let s10 := scratchHeaderConfiguration state h2 (entry + 10) (word width (base + 2 * n + 2)) (word width (base + 4 * n + 4)) (word width 4)
    programStep program s9 = some s10 := by
  let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
  let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
  let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
  let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
  have h1Size : h1.size = state.heap.size := by simp only [h1, Array.size_setIfInBounds]
  have h2Size : h2.size = state.heap.size := by simp only [h2, Array.size_setIfInBounds, h1Size]
  have h3Size : h3.size = state.heap.size := by simp only [h3, Array.size_setIfInBounds, h2Size]
  have h4Size : h4.size = state.heap.size := by simp only [h4, Array.size_setIfInBounds, h3Size]
  have bound0 : base + 2 * n < state.heap.size := by rw [sizeEq]; omega
  have bound1 : base + 2 * n + 1 < state.heap.size := by rw [sizeEq]; omega
  have bound2 : base + 2 * n + 2 < state.heap.size := by rw [sizeEq]; omega
  have bound3 : base + 2 * n + 3 < state.heap.size := by rw [sizeEq]; omega
  have add9 : base + 2 * n + 1 + 1 = base + 2 * n + 2 := by omega
  have addressFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have scalarRoom : base + 5 * n + 4 < 2 ^ width := by
    rw [← sizeEq]
    exact room
  let s9 := scratchHeaderConfiguration state h2 (entry + 9) (word width (base + 2 * n + 1)) (word width (base + 4 * n + 4)) (word width 4)
  let s10 := scratchHeaderConfiguration state h2 (entry + 10) (word width (base + 2 * n + 2)) (word width (base + 4 * n + 4)) (word width 4)
  have w4 : (word width (base + 2 * n + 1)).val = base + 2 * n + 1 := Nat.mod_eq_of_lt (by omega)
  have w12 : (word width (1)).val = 1 := Nat.mod_eq_of_lt (by omega)
  have pc9 : (word width (entry + 9)).val = entry + 9 := Nat.mod_eq_of_lt (addressFits 9 (by decide))
  have nextPC : entry + 9 + 1 = entry + 10 := by omega
  change programStep program s9 = some s10
  rw [fetched8 program s9 (entry + 9) (.add 0 0 5)
    (by rfl) (addressFits 9 (by decide))
    (by simpa [scratchHeaderCode] using present ⟨9, by decide⟩)]
  simp [s10, s9, scratchHeaderConfiguration, step, State.advance, State.put, running, baseWord, countWord, zero, one, w4, w12, pc9, add9, nextPC]
  all_goals first
    | rfl
    | (congr 1; funext register; fin_cases register <;> rfl)

private theorem scratch_header_transition_10 (program : Program width 8) (state : State width 8)
    (entry base n : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (baseWord : state.reg 3 = word width base)
    (countWord : state.reg 4 = word width n) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = word width 1) (sizeEq : state.heap.size = base + 5 * n + 4)
    (room : state.heap.size < 2 ^ width) (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? = (scratchHeaderCode width)[phase.val]?) :
    let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
    let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
    let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
    let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
    let s10 := scratchHeaderConfiguration state h2 (entry + 10) (word width (base + 2 * n + 2)) (word width (base + 4 * n + 4)) (word width 4)
    let s11 := scratchHeaderConfiguration state h2 (entry + 11) (word width (base + 2 * n + 2)) (word width (base + 5 * n + 4)) (word width 4)
    programStep program s10 = some s11 := by
  let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
  let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
  let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
  let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
  have h1Size : h1.size = state.heap.size := by simp only [h1, Array.size_setIfInBounds]
  have h2Size : h2.size = state.heap.size := by simp only [h2, Array.size_setIfInBounds, h1Size]
  have h3Size : h3.size = state.heap.size := by simp only [h3, Array.size_setIfInBounds, h2Size]
  have h4Size : h4.size = state.heap.size := by simp only [h4, Array.size_setIfInBounds, h3Size]
  have bound0 : base + 2 * n < state.heap.size := by rw [sizeEq]; omega
  have bound1 : base + 2 * n + 1 < state.heap.size := by rw [sizeEq]; omega
  have bound2 : base + 2 * n + 2 < state.heap.size := by rw [sizeEq]; omega
  have bound3 : base + 2 * n + 3 < state.heap.size := by rw [sizeEq]; omega
  have add10 : base + 4 * n + 4 + n = base + 5 * n + 4 := by omega
  have addressFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have scalarRoom : base + 5 * n + 4 < 2 ^ width := by
    rw [← sizeEq]
    exact room
  let s10 := scratchHeaderConfiguration state h2 (entry + 10) (word width (base + 2 * n + 2)) (word width (base + 4 * n + 4)) (word width 4)
  let s11 := scratchHeaderConfiguration state h2 (entry + 11) (word width (base + 2 * n + 2)) (word width (base + 5 * n + 4)) (word width 4)
  have w0 : (word width (n)).val = n := Nat.mod_eq_of_lt (by omega)
  have w9 : (word width (base + 4 * n + 4)).val = base + 4 * n + 4 := Nat.mod_eq_of_lt (by omega)
  have pc10 : (word width (entry + 10)).val = entry + 10 := Nat.mod_eq_of_lt (addressFits 10 (by decide))
  have nextPC : entry + 10 + 1 = entry + 11 := by omega
  change programStep program s10 = some s11
  rw [fetched8 program s10 (entry + 10) (.add 1 1 4)
    (by rfl) (addressFits 10 (by decide))
    (by simpa [scratchHeaderCode] using present ⟨10, by decide⟩)]
  simp [s11, s10, scratchHeaderConfiguration, step, State.advance, State.put, running, baseWord, countWord, zero, one, w0, w9, pc10, add10, nextPC]
  all_goals first
    | rfl
    | (congr 1; funext register; fin_cases register <;> rfl)

private theorem scratch_header_transition_11 (program : Program width 8) (state : State width 8)
    (entry base n : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (baseWord : state.reg 3 = word width base)
    (countWord : state.reg 4 = word width n) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = word width 1) (sizeEq : state.heap.size = base + 5 * n + 4)
    (room : state.heap.size < 2 ^ width) (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? = (scratchHeaderCode width)[phase.val]?) :
    let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
    let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
    let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
    let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
    let s11 := scratchHeaderConfiguration state h2 (entry + 11) (word width (base + 2 * n + 2)) (word width (base + 5 * n + 4)) (word width 4)
    let s12 := scratchHeaderConfiguration state h3 (entry + 12) (word width (base + 2 * n + 2)) (word width (base + 5 * n + 4)) (word width 4)
    programStep program s11 = some s12 := by
  let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
  let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
  let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
  let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
  have h1Size : h1.size = state.heap.size := by simp only [h1, Array.size_setIfInBounds]
  have h2Size : h2.size = state.heap.size := by simp only [h2, Array.size_setIfInBounds, h1Size]
  have h3Size : h3.size = state.heap.size := by simp only [h3, Array.size_setIfInBounds, h2Size]
  have h4Size : h4.size = state.heap.size := by simp only [h4, Array.size_setIfInBounds, h3Size]
  have bound0 : base + 2 * n < state.heap.size := by rw [sizeEq]; omega
  have bound1 : base + 2 * n + 1 < state.heap.size := by rw [sizeEq]; omega
  have bound2 : base + 2 * n + 2 < state.heap.size := by rw [sizeEq]; omega
  have bound3 : base + 2 * n + 3 < state.heap.size := by rw [sizeEq]; omega
  have addressFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have scalarRoom : base + 5 * n + 4 < 2 ^ width := by
    rw [← sizeEq]
    exact room
  let s11 := scratchHeaderConfiguration state h2 (entry + 11) (word width (base + 2 * n + 2)) (word width (base + 5 * n + 4)) (word width 4)
  let s12 := scratchHeaderConfiguration state h3 (entry + 12) (word width (base + 2 * n + 2)) (word width (base + 5 * n + 4)) (word width 4)
  have w5 : (word width (base + 2 * n + 2)).val = base + 2 * n + 2 := Nat.mod_eq_of_lt (by omega)
  have pc11 : (word width (entry + 11)).val = entry + 11 := Nat.mod_eq_of_lt (addressFits 11 (by decide))
  have nextPC : entry + 11 + 1 = entry + 12 := by omega
  change programStep program s11 = some s12
  rw [fetched8 program s11 (entry + 11) (.store 0 1)
    (by rfl) (addressFits 11 (by decide))
    (by simpa [scratchHeaderCode] using present ⟨11, by decide⟩)]
  simp [s12, s11, scratchHeaderConfiguration, step, State.advance, State.put, running, baseWord, countWord, zero, one, w5, pc11, h3, Array.setIfInBounds_def, h1Size, h2Size, h3Size, h4Size, bound0, bound1, bound2, bound3, nextPC]
  all_goals first
    | rfl
    | (congr 1; funext register; fin_cases register <;> rfl)

private theorem scratch_header_transition_12 (program : Program width 8) (state : State width 8)
    (entry base n : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (baseWord : state.reg 3 = word width base)
    (countWord : state.reg 4 = word width n) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = word width 1) (sizeEq : state.heap.size = base + 5 * n + 4)
    (room : state.heap.size < 2 ^ width) (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? = (scratchHeaderCode width)[phase.val]?) :
    let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
    let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
    let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
    let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
    let s12 := scratchHeaderConfiguration state h3 (entry + 12) (word width (base + 2 * n + 2)) (word width (base + 5 * n + 4)) (word width 4)
    let s13 := scratchHeaderConfiguration state h3 (entry + 13) (word width (base + 2 * n + 3)) (word width (base + 5 * n + 4)) (word width 4)
    programStep program s12 = some s13 := by
  let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
  let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
  let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
  let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
  have h1Size : h1.size = state.heap.size := by simp only [h1, Array.size_setIfInBounds]
  have h2Size : h2.size = state.heap.size := by simp only [h2, Array.size_setIfInBounds, h1Size]
  have h3Size : h3.size = state.heap.size := by simp only [h3, Array.size_setIfInBounds, h2Size]
  have h4Size : h4.size = state.heap.size := by simp only [h4, Array.size_setIfInBounds, h3Size]
  have bound0 : base + 2 * n < state.heap.size := by rw [sizeEq]; omega
  have bound1 : base + 2 * n + 1 < state.heap.size := by rw [sizeEq]; omega
  have bound2 : base + 2 * n + 2 < state.heap.size := by rw [sizeEq]; omega
  have bound3 : base + 2 * n + 3 < state.heap.size := by rw [sizeEq]; omega
  have add12 : base + 2 * n + 2 + 1 = base + 2 * n + 3 := by omega
  have addressFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have scalarRoom : base + 5 * n + 4 < 2 ^ width := by
    rw [← sizeEq]
    exact room
  let s12 := scratchHeaderConfiguration state h3 (entry + 12) (word width (base + 2 * n + 2)) (word width (base + 5 * n + 4)) (word width 4)
  let s13 := scratchHeaderConfiguration state h3 (entry + 13) (word width (base + 2 * n + 3)) (word width (base + 5 * n + 4)) (word width 4)
  have w5 : (word width (base + 2 * n + 2)).val = base + 2 * n + 2 := Nat.mod_eq_of_lt (by omega)
  have w12 : (word width (1)).val = 1 := Nat.mod_eq_of_lt (by omega)
  have pc12 : (word width (entry + 12)).val = entry + 12 := Nat.mod_eq_of_lt (addressFits 12 (by decide))
  have nextPC : entry + 12 + 1 = entry + 13 := by omega
  change programStep program s12 = some s13
  rw [fetched8 program s12 (entry + 12) (.add 0 0 5)
    (by rfl) (addressFits 12 (by decide))
    (by simpa [scratchHeaderCode] using present ⟨12, by decide⟩)]
  simp [s13, s12, scratchHeaderConfiguration, step, State.advance, State.put, running, baseWord, countWord, zero, one, w5, w12, pc12, add12, nextPC]
  all_goals first
    | rfl
    | (congr 1; funext register; fin_cases register <;> rfl)

private theorem scratch_header_transition_13 (program : Program width 8) (state : State width 8)
    (entry base n : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (baseWord : state.reg 3 = word width base)
    (countWord : state.reg 4 = word width n) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = word width 1) (sizeEq : state.heap.size = base + 5 * n + 4)
    (room : state.heap.size < 2 ^ width) (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? = (scratchHeaderCode width)[phase.val]?) :
    let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
    let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
    let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
    let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
    let s13 := scratchHeaderConfiguration state h3 (entry + 13) (word width (base + 2 * n + 3)) (word width (base + 5 * n + 4)) (word width 4)
    let s14 := scratchHeaderConfiguration state h4 (entry + 14) (word width (base + 2 * n + 3)) (word width (base + 5 * n + 4)) (word width 4)
    programStep program s13 = some s14 := by
  let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
  let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
  let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
  let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
  have h1Size : h1.size = state.heap.size := by simp only [h1, Array.size_setIfInBounds]
  have h2Size : h2.size = state.heap.size := by simp only [h2, Array.size_setIfInBounds, h1Size]
  have h3Size : h3.size = state.heap.size := by simp only [h3, Array.size_setIfInBounds, h2Size]
  have h4Size : h4.size = state.heap.size := by simp only [h4, Array.size_setIfInBounds, h3Size]
  have bound0 : base + 2 * n < state.heap.size := by rw [sizeEq]; omega
  have bound1 : base + 2 * n + 1 < state.heap.size := by rw [sizeEq]; omega
  have bound2 : base + 2 * n + 2 < state.heap.size := by rw [sizeEq]; omega
  have bound3 : base + 2 * n + 3 < state.heap.size := by rw [sizeEq]; omega
  have addressFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have scalarRoom : base + 5 * n + 4 < 2 ^ width := by
    rw [← sizeEq]
    exact room
  let s13 := scratchHeaderConfiguration state h3 (entry + 13) (word width (base + 2 * n + 3)) (word width (base + 5 * n + 4)) (word width 4)
  let s14 := scratchHeaderConfiguration state h4 (entry + 14) (word width (base + 2 * n + 3)) (word width (base + 5 * n + 4)) (word width 4)
  have w6 : (word width (base + 2 * n + 3)).val = base + 2 * n + 3 := Nat.mod_eq_of_lt (by omega)
  have w11 : (word width (0)).val = 0 := Nat.mod_eq_of_lt (by omega)
  have pc13 : (word width (entry + 13)).val = entry + 13 := Nat.mod_eq_of_lt (addressFits 13 (by decide))
  have nextPC : entry + 13 + 1 = entry + 14 := by omega
  change programStep program s13 = some s14
  rw [fetched8 program s13 (entry + 13) (.store 0 2)
    (by rfl) (addressFits 13 (by decide))
    (by simpa [scratchHeaderCode] using present ⟨13, by decide⟩)]
  simp [s14, s13, scratchHeaderConfiguration, step, State.advance, State.put, running, baseWord, countWord, zero, one, w6, w11, pc13, h4, Array.setIfInBounds_def, h1Size, h2Size, h3Size, h4Size, bound0, bound1, bound2, bound3, nextPC]
  all_goals first
    | rfl
    | (congr 1; funext register; fin_cases register <;> rfl)

private theorem scratch_header_transition_14 (program : Program width 8) (state : State width 8)
    (entry base n : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (baseWord : state.reg 3 = word width base)
    (countWord : state.reg 4 = word width n) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = word width 1) (sizeEq : state.heap.size = base + 5 * n + 4)
    (room : state.heap.size < 2 ^ width) (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? = (scratchHeaderCode width)[phase.val]?) :
    let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
    let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
    let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
    let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
    let s14 := scratchHeaderConfiguration state h4 (entry + 14) (word width (base + 2 * n + 3)) (word width (base + 5 * n + 4)) (word width 4)
    let s15 := scratchHeaderConfiguration state h4 (entry + 15) (word width (base + 2 * n + 3)) (word width (base + 5 * n + 4)) (word width (2 ^ width - 1))
    programStep program s14 = some s15 := by
  let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
  let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
  let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
  let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
  have h1Size : h1.size = state.heap.size := by simp only [h1, Array.size_setIfInBounds]
  have h2Size : h2.size = state.heap.size := by simp only [h2, Array.size_setIfInBounds, h1Size]
  have h3Size : h3.size = state.heap.size := by simp only [h3, Array.size_setIfInBounds, h2Size]
  have h4Size : h4.size = state.heap.size := by simp only [h4, Array.size_setIfInBounds, h3Size]
  have bound0 : base + 2 * n < state.heap.size := by rw [sizeEq]; omega
  have bound1 : base + 2 * n + 1 < state.heap.size := by rw [sizeEq]; omega
  have bound2 : base + 2 * n + 2 < state.heap.size := by rw [sizeEq]; omega
  have bound3 : base + 2 * n + 3 < state.heap.size := by rw [sizeEq]; omega
  have addressFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have scalarRoom : base + 5 * n + 4 < 2 ^ width := by
    rw [← sizeEq]
    exact room
  let s14 := scratchHeaderConfiguration state h4 (entry + 14) (word width (base + 2 * n + 3)) (word width (base + 5 * n + 4)) (word width 4)
  let s15 := scratchHeaderConfiguration state h4 (entry + 15) (word width (base + 2 * n + 3)) (word width (base + 5 * n + 4)) (word width (2 ^ width - 1))
  have pc14 : (word width (entry + 14)).val = entry + 14 := Nat.mod_eq_of_lt (addressFits 14 (by decide))
  have nextPC : entry + 14 + 1 = entry + 15 := by omega
  change programStep program s14 = some s15
  rw [fetched8 program s14 (entry + 14) (.constant 6 (word width (2 ^ width - 1)))
    (by rfl) (addressFits 14 (by decide))
    (by simpa [scratchHeaderCode] using present ⟨14, by decide⟩)]
  simp [s15, s14, scratchHeaderConfiguration, step, State.advance, State.put, running, baseWord, countWord, zero, one, pc14, nextPC]
  all_goals first
    | rfl
    | (congr 1; funext register; fin_cases register <;> rfl)

/-- Fifteen fetched steps form the scratch cursor headers from actual runtime
registers. Flat proof configurations retain the exact executed state fields. -/
theorem scratch_header_execution (program : Program width 8) (state : State width 8)
    (entry base n : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (baseWord : state.reg 3 = word width base)
    (countWord : state.reg 4 = word width n) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = word width 1) (sizeEq : state.heap.size = base + 5 * n + 4)
    (room : state.heap.size < 2 ^ width) (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? = (scratchHeaderCode width)[phase.val]?) :
    let final := scratchHeaderState state base n
    Execution program state final 15 state.liveWords ∧
      final.heap = scratchHeaderHeap state.heap base n ∧
      final.reg 2 = word width 0 ∧ final.reg 5 = word width 1 ∧
      final.reg 6 = word width (2 ^ width - 1) ∧ final.reg 7 = state.reg 7 ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 15) ∧ final.halted = false := by
  let h1 := state.heap.setIfInBounds (base + 2 * n) (word width (base + 3 * n + 4))
  let h2 := h1.setIfInBounds (base + 2 * n + 1) (word width (base + 4 * n + 4))
  let h3 := h2.setIfInBounds (base + 2 * n + 2) (word width (base + 5 * n + 4))
  let h4 := h3.setIfInBounds (base + 2 * n + 3) (word width 0)
  let s1 := scratchHeaderConfiguration state state.heap (entry + 1) (word width (2 * n)) (state.reg 1) (state.reg 6)
  let s2 := scratchHeaderConfiguration state state.heap (entry + 2) (word width (base + 2 * n)) (state.reg 1) (state.reg 6)
  let s3 := scratchHeaderConfiguration state state.heap (entry + 3) (word width (base + 2 * n)) (word width (base + 3 * n)) (state.reg 6)
  let s4 := scratchHeaderConfiguration state state.heap (entry + 4) (word width (base + 2 * n)) (word width (base + 3 * n)) (word width 4)
  let s5 := scratchHeaderConfiguration state state.heap (entry + 5) (word width (base + 2 * n)) (word width (base + 3 * n + 4)) (word width 4)
  let s6 := scratchHeaderConfiguration state h1 (entry + 6) (word width (base + 2 * n)) (word width (base + 3 * n + 4)) (word width 4)
  let s7 := scratchHeaderConfiguration state h1 (entry + 7) (word width (base + 2 * n + 1)) (word width (base + 3 * n + 4)) (word width 4)
  let s8 := scratchHeaderConfiguration state h1 (entry + 8) (word width (base + 2 * n + 1)) (word width (base + 4 * n + 4)) (word width 4)
  let s9 := scratchHeaderConfiguration state h2 (entry + 9) (word width (base + 2 * n + 1)) (word width (base + 4 * n + 4)) (word width 4)
  let s10 := scratchHeaderConfiguration state h2 (entry + 10) (word width (base + 2 * n + 2)) (word width (base + 4 * n + 4)) (word width 4)
  let s11 := scratchHeaderConfiguration state h2 (entry + 11) (word width (base + 2 * n + 2)) (word width (base + 5 * n + 4)) (word width 4)
  let s12 := scratchHeaderConfiguration state h3 (entry + 12) (word width (base + 2 * n + 2)) (word width (base + 5 * n + 4)) (word width 4)
  let s13 := scratchHeaderConfiguration state h3 (entry + 13) (word width (base + 2 * n + 3)) (word width (base + 5 * n + 4)) (word width 4)
  let s14 := scratchHeaderConfiguration state h4 (entry + 14) (word width (base + 2 * n + 3)) (word width (base + 5 * n + 4)) (word width 4)
  let s15 := scratchHeaderConfiguration state h4 (entry + 15) (word width (base + 2 * n + 3)) (word width (base + 5 * n + 4)) (word width (2 ^ width - 1))
  have pcValue : state.pc.val = entry := by
    rw [position]
    exact Nat.mod_eq_of_lt (by omega)
  have t0 : programStep program state = some s1 := scratch_header_transition_0 program state entry base n position running baseWord countWord zero one sizeEq room capacity present
  have t1 : programStep program s1 = some s2 := scratch_header_transition_1 program state entry base n position running baseWord countWord zero one sizeEq room capacity present
  have t2 : programStep program s2 = some s3 := scratch_header_transition_2 program state entry base n position running baseWord countWord zero one sizeEq room capacity present
  have t3 : programStep program s3 = some s4 := scratch_header_transition_3 program state entry base n position running baseWord countWord zero one sizeEq room capacity present
  have t4 : programStep program s4 = some s5 := scratch_header_transition_4 program state entry base n position running baseWord countWord zero one sizeEq room capacity present
  have t5 : programStep program s5 = some s6 := scratch_header_transition_5 program state entry base n position running baseWord countWord zero one sizeEq room capacity present
  have t6 : programStep program s6 = some s7 := scratch_header_transition_6 program state entry base n position running baseWord countWord zero one sizeEq room capacity present
  have t7 : programStep program s7 = some s8 := scratch_header_transition_7 program state entry base n position running baseWord countWord zero one sizeEq room capacity present
  have t8 : programStep program s8 = some s9 := scratch_header_transition_8 program state entry base n position running baseWord countWord zero one sizeEq room capacity present
  have t9 : programStep program s9 = some s10 := scratch_header_transition_9 program state entry base n position running baseWord countWord zero one sizeEq room capacity present
  have t10 : programStep program s10 = some s11 := scratch_header_transition_10 program state entry base n position running baseWord countWord zero one sizeEq room capacity present
  have t11 : programStep program s11 = some s12 := scratch_header_transition_11 program state entry base n position running baseWord countWord zero one sizeEq room capacity present
  have t12 : programStep program s12 = some s13 := scratch_header_transition_12 program state entry base n position running baseWord countWord zero one sizeEq room capacity present
  have t13 : programStep program s13 = some s14 := scratch_header_transition_13 program state entry base n position running baseWord countWord zero one sizeEq room capacity present
  have t14 : programStep program s14 = some s15 := scratch_header_transition_14 program state entry base n position running baseWord countWord zero one sizeEq room capacity present
  have live1 : s1.liveWords = state.liveWords := by
    simp only [s1, scratchHeaderConfiguration, State.liveWords, h1, h2, h3, h4, Array.size_setIfInBounds]
  have live2 : s2.liveWords = state.liveWords := by
    simp only [s2, scratchHeaderConfiguration, State.liveWords, h1, h2, h3, h4, Array.size_setIfInBounds]
  have live3 : s3.liveWords = state.liveWords := by
    simp only [s3, scratchHeaderConfiguration, State.liveWords, h1, h2, h3, h4, Array.size_setIfInBounds]
  have live4 : s4.liveWords = state.liveWords := by
    simp only [s4, scratchHeaderConfiguration, State.liveWords, h1, h2, h3, h4, Array.size_setIfInBounds]
  have live5 : s5.liveWords = state.liveWords := by
    simp only [s5, scratchHeaderConfiguration, State.liveWords, h1, h2, h3, h4, Array.size_setIfInBounds]
  have live6 : s6.liveWords = state.liveWords := by
    simp only [s6, scratchHeaderConfiguration, State.liveWords, h1, h2, h3, h4, Array.size_setIfInBounds]
  have live7 : s7.liveWords = state.liveWords := by
    simp only [s7, scratchHeaderConfiguration, State.liveWords, h1, h2, h3, h4, Array.size_setIfInBounds]
  have live8 : s8.liveWords = state.liveWords := by
    simp only [s8, scratchHeaderConfiguration, State.liveWords, h1, h2, h3, h4, Array.size_setIfInBounds]
  have live9 : s9.liveWords = state.liveWords := by
    simp only [s9, scratchHeaderConfiguration, State.liveWords, h1, h2, h3, h4, Array.size_setIfInBounds]
  have live10 : s10.liveWords = state.liveWords := by
    simp only [s10, scratchHeaderConfiguration, State.liveWords, h1, h2, h3, h4, Array.size_setIfInBounds]
  have live11 : s11.liveWords = state.liveWords := by
    simp only [s11, scratchHeaderConfiguration, State.liveWords, h1, h2, h3, h4, Array.size_setIfInBounds]
  have live12 : s12.liveWords = state.liveWords := by
    simp only [s12, scratchHeaderConfiguration, State.liveWords, h1, h2, h3, h4, Array.size_setIfInBounds]
  have live13 : s13.liveWords = state.liveWords := by
    simp only [s13, scratchHeaderConfiguration, State.liveWords, h1, h2, h3, h4, Array.size_setIfInBounds]
  have live14 : s14.liveWords = state.liveWords := by
    simp only [s14, scratchHeaderConfiguration, State.liveWords, h1, h2, h3, h4, Array.size_setIfInBounds]
  have live15 : s15.liveWords = state.liveWords := by
    simp only [s15, scratchHeaderConfiguration, State.liveWords, h1, h2, h3, h4, Array.size_setIfInBounds]
  have chunk0 : Execution program state s3 3 state.liveWords := by
    convert Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl s3))) using 1 <;>
      (try simp only [live1, live2, live3, Nat.max_self])
  have chunk1 : Execution program s3 s6 3 state.liveWords := by
    convert Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.refl s6))) using 1 <;>
      (try simp only [live3, live4, live5, live6, Nat.max_self])
  have chunk2 : Execution program s6 s9 3 state.liveWords := by
    convert Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.refl s9))) using 1 <;>
      (try simp only [live6, live7, live8, live9, Nat.max_self])
  have chunk3 : Execution program s9 s12 3 state.liveWords := by
    convert Execution.cons t9 (Execution.cons t10 (Execution.cons t11 (Execution.refl s12))) using 1 <;>
      (try simp only [live9, live10, live11, live12, Nat.max_self])
  have chunk4 : Execution program s12 s15 3 state.liveWords := by
    convert Execution.cons t12 (Execution.cons t13 (Execution.cons t14 (Execution.refl s15))) using 1 <;>
      (try simp only [live12, live13, live14, live15, Nat.max_self])
  have trace : Execution program state s15 15 state.liveWords := by
    convert (((chunk0.append chunk1).append chunk2).append chunk3).append chunk4 using 1 <;>
      simp only [Nat.max_self]
  have endpoint : scratchHeaderState state base n = s15 := by
    simp only [scratchHeaderState, s15, scratchHeaderHeap, pcValue, h4, h3, h2, h1]
  rw [endpoint]
  refine ⟨trace, ?_⟩
  simp [s15, scratchHeaderConfiguration, h4, h3, h2, h1, scratchHeaderHeap, zero, one, running]

private theorem marks_store (heap : Array (Word width)) (marks : Controller.Horn.Worklist.IndexedNormalize.Marks n)
    (base header : Nat) (value : Word width)
    (stored : Controller.Horn.MarkStorage.Stored marks base heap)
    (bound : header < heap.size) (above : base + 2 * n ≤ header) :
    Controller.Horn.MarkStorage.Stored marks base (heap.setIfInBounds header value) := by
  refine ⟨by simpa only [Array.size_setIfInBounds] using stored.fits, ?_⟩
  intro literal
  have different : header ≠ Controller.Horn.MarkStorage.address base literal := by
    have := Controller.Horn.MarkStorage.address_lt base literal
    omega
  simpa only [Array.setIfInBounds_def, dite_eq_left bound] using
    (Array.getElem_set_ne bound (stored.bound literal) different).trans (stored.entry literal)

/-- Scratch header writes are disjoint from the actual mark representation. -/
theorem scratch_header_marks (heap : Array (Word width)) (base : Nat)
    (marks : Controller.Horn.Worklist.IndexedNormalize.Marks n)
    (stored : Controller.Horn.MarkStorage.Stored marks base heap)
    (sizeEq : heap.size = base + 5 * n + 4) :
    Controller.Horn.MarkStorage.Stored marks base (scratchHeaderHeap heap base n) := by
  have first := marks_store heap marks base (base + 2 * n) (word width (base + 3 * n + 4))
    stored (by omega) (by omega)
  have second := marks_store _ marks base (base + 2 * n + 1) (word width (base + 4 * n + 4))
    first (by simp only [Array.size_setIfInBounds]; omega) (by omega)
  have third := marks_store _ marks base (base + 2 * n + 2) (word width (base + 5 * n + 4))
    second (by simp only [Array.size_setIfInBounds]; omega) (by omega)
  exact marks_store _ marks base (base + 2 * n + 3) (word width 0)
    third (by simp only [Array.size_setIfInBounds]; omega) (by omega)

theorem scratch_header_cells (heap : Array (Word width)) (base n : Nat)
    (sizeEq : heap.size = base + 5 * n + 4) :
    let final := scratchHeaderHeap heap base n
    final[base + 2 * n]? = some (word width (base + 3 * n + 4)) ∧
      final[base + 2 * n + 1]? = some (word width (base + 4 * n + 4)) ∧
      final[base + 2 * n + 2]? = some (word width (base + 5 * n + 4)) ∧
      final[base + 2 * n + 3]? = some (word width 0) := by
  dsimp only [scratchHeaderHeap]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Array.getElem?_setIfInBounds_ne (by omega),
      Array.getElem?_setIfInBounds_ne (by omega), Array.getElem?_setIfInBounds_ne (by omega),
      Array.getElem?_setIfInBounds_self_of_lt (by omega)]
  · rw [Array.getElem?_setIfInBounds_ne (by omega), Array.getElem?_setIfInBounds_ne (by omega),
      Array.getElem?_setIfInBounds_self_of_lt (by simp only [Array.size_setIfInBounds]; omega)]
  · rw [Array.getElem?_setIfInBounds_ne (by omega),
      Array.getElem?_setIfInBounds_self_of_lt (by simp only [Array.size_setIfInBounds]; omega)]
  · rw [Array.getElem?_setIfInBounds_self_of_lt (by simp only [Array.size_setIfInBounds]; omega)]

/-- Every original source cell lies strictly before the scratch header stores. -/
theorem scratch_header_prefix (heap : Array (Word width)) (base n : Nat) (cell : Nat)
    (before : cell < base) :
    (scratchHeaderHeap heap base n)[cell]? = heap[cell]? := by
  unfold scratchHeaderHeap
  rw [Array.getElem?_setIfInBounds_ne (by omega), Array.getElem?_setIfInBounds_ne (by omega),
    Array.getElem?_setIfInBounds_ne (by omega), Array.getElem?_setIfInBounds_ne (by omega)]

/-- The executed cursor stores and actual zero allocation give all clean-row
fields, including the zero conflict flag and all finite mark cells. -/
theorem scratch_header_row (heap : Array (Word width)) (base : Nat)
    (marks : Controller.Horn.Worklist.IndexedNormalize.Marks n)
    (stored : Controller.Horn.MarkStorage.Stored marks base heap)
    (sizeEq : heap.size = base + 5 * n + 4) :
    Controller.Horn.LiteralDispatch.RowStored
      (Controller.Horn.Worklist.IndexedNormalize.Row.empty marks) base
      (base + 3 * n + 4) (base + 4 * n + 4) (base + 5 * n + 4)
      (scratchHeaderHeap heap base n) := by
  obtain ⟨positive, negative, touched, flag⟩ := scratch_header_cells heap base n sizeEq
  exact Controller.Horn.HeaderReuse.empty_row_stored marks base _
    (scratch_header_marks heap base marks stored sizeEq)
    (by rw [scratchHeaderHeap_size, sizeEq]) positive negative touched flag


/-- The actual saved boundary is moved above the reset pointer and used as the
query record-header address. It remains on the stack for captured cleanup. -/
def scratchEndpointCode : Array (Instruction width 8) :=
  #[.pop 0, .pop 1, .push 0, .push 1, .store 1 7]

@[simp] theorem scratchEndpointCode_size : (scratchEndpointCode (width := width)).size = 5 := rfl

def scratchEndpointState (state : State width 8) (keep inverse : Nat)
    (rest : List (Word width)) : State width 8 :=
  let first := ({ state.advance with stack := word width keep :: rest }).put 0 (word width inverse)
  let second := ({ first.advance with stack := rest }).put 1 (word width keep)
  let third := { second.advance with stack := word width inverse :: rest }
  let fourth := { third.advance with stack := word width keep :: word width inverse :: rest }
  { fourth.advance with heap := fourth.heap.setIfInBounds keep (word width state.heap.size) }

/-- Five fetched steps retain both saved words and store the endpoint obtained
from the actual tracked allocation register. -/
theorem scratch_endpoint_execution (program : Program width 8) (state : State width 8)
    (entry keep inverse : Nat) (rest : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (saved : state.stack = word width inverse :: word width keep :: rest)
    (pointer : state.reg 7 = word width state.heap.size) (bound : keep < state.heap.size)
    (room : state.heap.size < 2 ^ width) (capacity : entry + 5 < 2 ^ width)
    (present : ∀ phase : Fin 5, program[entry + phase.val]? =
      (scratchEndpointCode (width := width))[phase.val]?) :
    let final := scratchEndpointState state keep inverse rest
    Execution program state final 5 state.liveWords ∧
      final.heap = state.heap.setIfInBounds keep (word width state.heap.size) ∧
      final.stack = word width keep :: word width inverse :: rest ∧
      final.output = state.output ∧ final.pc = word width (entry + 5) ∧
      final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → final.reg register = state.reg register) := by
  let s1 := ({ state.advance with stack := word width keep :: rest }).put 0 (word width inverse)
  let s2 := ({ s1.advance with stack := rest }).put 1 (word width keep)
  let s3 := { s2.advance with stack := word width inverse :: rest }
  let s4 := { s3.advance with stack := word width keep :: word width inverse :: rest }
  let s5 := { s4.advance with heap := s4.heap.setIfInBounds keep (word width state.heap.size) }
  have p1 : s1.pc = word width (entry + 1) := by
    simpa only [s1, State.put] using advance8_pc state entry position (by omega)
  have p2 : s2.pc = word width (entry + 2) := by
    simpa only [s2, State.put, Nat.add_assoc] using advance8_pc s1 (entry + 1) p1 (by omega)
  have p3 : s3.pc = word width (entry + 3) := by
    simpa only [s3, Nat.add_assoc] using advance8_pc s2 (entry + 2) p2 (by omega)
  have p4 : s4.pc = word width (entry + 4) := by
    simpa only [s4, Nat.add_assoc] using advance8_pc s3 (entry + 3) p3 (by omega)
  have p5 : s5.pc = word width (entry + 5) := by
    simpa only [s5, Nat.add_assoc] using advance8_pc s4 (entry + 4) p4 (by omega)
  have t0 : programStep program state = some s1 := by
    rw [fetched8 program state entry (.pop 0) position (by omega)
      (by simpa [scratchEndpointCode] using present ⟨0, by decide⟩)]
    simp only [step, running, Bool.false_eq_true, ite_false, saved]
    rfl
  have t1 : programStep program s1 = some s2 := by
    rw [fetched8 program s1 (entry + 1) (.pop 1) p1 (by omega)
      (by simpa [scratchEndpointCode] using present ⟨1, by decide⟩)]
    simp [step, s1, s2, State.put, State.advance, running]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched8 program s2 (entry + 2) (.push 0) p2 (by omega)
      (by simpa [scratchEndpointCode] using present ⟨2, by decide⟩)]
    change (if s2.halted then none else some { s2.advance with stack := s2.reg 0 :: s2.stack }) = some s3
    have active : s2.halted = false := by simp only [s2, s1, State.put, State.advance, running]
    have value : s2.reg 0 = word width inverse := by simp [s2, s1, State.put, State.advance]
    rw [active, value]
    rfl
  have t3 : programStep program s3 = some s4 := by
    rw [fetched8 program s3 (entry + 3) (.push 1) p3 (by omega)
      (by simpa [scratchEndpointCode] using present ⟨3, by decide⟩)]
    change (if s3.halted then none else some { s3.advance with stack := s3.reg 1 :: s3.stack }) = some s4
    have active : s3.halted = false := by simp only [s3, s2, s1, State.put, State.advance, running]
    have value : s3.reg 1 = word width keep := by simp [s3, s2, State.put, State.advance]
    rw [active, value]
    rfl
  have t4 : programStep program s4 = some s5 := by
    rw [fetched8 program s4 (entry + 4) (.store 1 7) p4 (by omega)
      (by simpa [scratchEndpointCode] using present ⟨4, by decide⟩)]
    change (if s4.halted then none else
      if h : (s4.reg 1).val < s4.heap.size then
        some { s4.advance with heap := s4.heap.set (s4.reg 1).val (s4.reg 7) h }
      else none) = some s5
    have active : s4.halted = false := by simp only [s4, s3, s2, s1, State.put, State.advance, running]
    have address : s4.reg 1 = word width keep := by simp [s4, s3, s2, State.put, State.advance]
    have value : s4.reg 7 = word width state.heap.size := by simp [s4, s3, s2, s1, State.put, State.advance, pointer]
    have actualBound : keep < s4.heap.size := bound
    rw [active, address, value, show (word width keep).val = keep from Nat.mod_eq_of_lt (by omega), dite_eq_left actualBound]
    simp only [s5, Array.setIfInBounds_def, dite_eq_left actualBound, Bool.false_eq_true, ite_false]
  have initialLive : state.liveWords = 11 + state.heap.size + rest.length + state.output.length := by
    simp only [State.liveWords, saved, List.length_cons]
    omega
  have live0 : state.liveWords = 11 + state.heap.size + rest.length + state.output.length := initialLive
  have live1 : s1.liveWords = 10 + state.heap.size + rest.length + state.output.length := by
    simp [s1, State.liveWords, State.put, State.advance, Nat.add_assoc] <;> omega
  have live2 : s2.liveWords = 9 + state.heap.size + rest.length + state.output.length := by
    simp [s2, s1, State.liveWords, State.put, State.advance, Nat.add_assoc] <;> omega
  have live3 : s3.liveWords = 10 + state.heap.size + rest.length + state.output.length := by
    simp [s3, s2, s1, State.liveWords, State.put, State.advance, Nat.add_assoc] <;> omega
  have live4 : s4.liveWords = state.liveWords := by
    simp [s4, s3, s2, s1, State.liveWords, State.put, State.advance, saved, Nat.add_assoc]
  have live5 : s5.liveWords = state.liveWords := by
    simp [s5, s4, s3, s2, s1, State.liveWords, State.put, State.advance,
      saved, Nat.add_assoc]
  have first : Execution program state s2 2 state.liveWords := by
    convert Execution.cons t0 (Execution.cons t1 (Execution.refl s2)) using 1 <;>
      (try simp only [live1, live2, live0]) <;> omega
  have last : Execution program s2 s5 3 state.liveWords := by
    convert Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.refl s5))) using 1 <;>
      (try simp only [live5, live4, Nat.max_self, live3, live2, live0]) <;> omega
  have trace : Execution program state s5 5 state.liveWords := by
    simpa only [Nat.max_self] using first.append last
  refine ⟨trace, rfl, rfl, rfl, p5, ?_, ?_⟩
  · simp [scratchEndpointState, s1, s2, s3, s4, s5, State.put, State.advance, running]
  · intro register notZero notOne
    simp [scratchEndpointState, s1, s2, s3, s4, s5, State.put, State.advance, notZero, notOne]


/-- The full runtime scratch phase forms its count, allocates, writes cursor
headers, and rotates the physically saved keep word into the backend position.
Its source representation and initial normalization invariant are derived on
the same executed heap; no initialized scratch or endpoint is supplied. -/
theorem scratch_initial_execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (clauses : List (Clause (Fin n)))
    (layout : Controller.Horn.SourceDirectory.Layout clauses)
    (represented : Stored clauses layout.directory layout.source state.heap)
    (directoryCursor : CursorStored layout.directory layout.directoryHeader state.heap)
    (directoryEnd : CursorStored (layout.directory + 2 * clauses.length) layout.endHeader state.heap)
    (baseEq : layout.base = state.heap.size)
    (position : state.pc = word width entry) (running : state.halted = false)
    (localCount : state.reg 2 = word width n) (pointer : state.reg 1 = word width state.heap.size)
    (inverse : Nat) (rest : List (Word width))
    (saved : state.stack = word width inverse :: word width layout.recordHeader :: rest)
    (capacity : entry + 36 < 2 ^ width) (room : state.heap.size + 5 * n + 4 < 2 ^ width)
    (countAt : ∀ phase : Fin 11, program[entry + phase.val]? = (scratchCountCode width)[phase.val]?)
    (allocateAt : Controller.Horn.TrackedAllocate.CodeAt program (entry + 11))
    (headersAt : ∀ phase : Fin 15, program[entry + 16 + phase.val]? = (scratchHeaderCode width)[phase.val]?)
    (endpointAt : ∀ phase : Fin 5, program[entry + 31 + phase.val]? =
      (scratchEndpointCode (width := width))[phase.val]?) :
    ∃ final : State width 8,
      Execution program state final (25 * n + 52) (state.liveWords + 5 * n + 4) ∧
      Controller.Horn.NormalizeLoop.Invariant clauses layout (state.heap.size + 5 * n + 4)
        0 (Controller.Horn.Worklist.IndexedNormalize.Marks.initial n) final ∧
      final.pc = word width (entry + 36) ∧
      final.stack = word width layout.recordHeader :: word width inverse :: rest ∧
      final.output = state.output ∧
      (∀ cell, cell < layout.recordHeader → final.heap[cell]? = state.heap[cell]?) ∧
      final.reg 4 = word width n ∧ final.reg 3 = word width state.heap.size := by
  obtain ⟨allocated, allocatedTrace, allocatedHeap, allocatedZero, allocatedBase,
    allocatedCount, allocatedOne, allocatedMask, allocatedPointer, allocatedPC,
    allocatedRunning, allocatedStack, allocatedOutput⟩ :=
    scratch_allocate_execution program state entry n position running localCount pointer
      (by omega) room countAt allocateAt
  have allocatedSize : allocated.heap.size = state.heap.size + 5 * n + 4 := by
    rw [allocatedHeap, Array.size_append, Array.size_replicate]
    omega
  obtain ⟨headerTrace, headerHeap, headerZero, headerOne, headerMask, headerPointer,
    headerStack, headerOutput, headerPC, headerRunning⟩ :=
    scratch_header_execution program allocated (entry + 16) state.heap.size n allocatedPC
      allocatedRunning allocatedBase allocatedCount allocatedZero allocatedOne allocatedSize
      (by rw [allocatedSize]; exact room) (by omega) headersAt
  let headered := scratchHeaderState allocated state.heap.size n
  have headerSize : headered.heap.size = state.heap.size + 5 * n + 4 := by
    rw [headerHeap, scratchHeaderHeap_size]
    exact allocatedSize
  have recordBefore : layout.recordHeader < state.heap.size := by
    have h := layout.headersBefore layout.recordHeader (by simp)
    have d := layout.directoryBefore
    have s := layout.sourceBefore
    have a : layout.source ≤ sourceOffset clauses layout.source clauses.length := by
      unfold sourceOffset
      omega
    omega
  obtain ⟨endpointTrace, endpointHeap, endpointStack, endpointOutput, endpointPC,
    endpointRunning, endpointRegisters⟩ :=
    scratch_endpoint_execution program headered (entry + 31) layout.recordHeader inverse rest
      (by simpa only [Nat.add_assoc] using headerPC) headerRunning
      (headerStack.trans (allocatedStack.trans saved))
      (by rw [headerPointer, allocatedPointer, headerSize])
      (by rw [headerSize]; omega) (by rw [headerSize]; exact room) (by omega) endpointAt
  let final := scratchEndpointState headered layout.recordHeader inverse rest
  have finalHeap : final.heap =
      (scratchHeaderHeap (state.heap ++ Array.replicate (5 * n + 4) (word width 0))
        state.heap.size n).setIfInBounds layout.recordHeader
        (word width (state.heap.size + 5 * n + 4)) := by
    rw [endpointHeap, headerSize, headerHeap, allocatedHeap]
  have finalSize : final.heap.size = state.heap.size + 5 * n + 4 := by
    rw [finalHeap, Array.size_setIfInBounds, scratchHeaderHeap_size,
      Array.size_append, Array.size_replicate]
    omega
  have allocatedLive : allocated.liveWords = state.liveWords + 5 * n + 4 := by
    unfold State.liveWords
    rw [allocatedSize, allocatedStack, allocatedOutput]
    omega
  have headerLive : headered.liveWords = state.liveWords + 5 * n + 4 := by
    unfold State.liveWords
    rw [headerSize, headerStack, headerOutput, allocatedStack, allocatedOutput]
    omega
  have joined : Execution program state final (25 * n + 52)
      (state.liveWords + 5 * n + 4) := by
    convert (allocatedTrace.append headerTrace).append endpointTrace using 1 <;>
      (try simp only [allocatedLive, headerLive, Nat.max_self]) <;> omega
  have lowFrame : ∀ cell, cell < state.heap.size → cell ≠ layout.recordHeader →
      final.heap[cell]? = state.heap[cell]? := by
    intro cell before different
    rw [finalHeap, Array.getElem?_setIfInBounds_ne (Ne.symm different),
      scratch_header_prefix _ state.heap.size n cell before,
      Array.getElem?_append_left before]
  have growing : state.heap.size ≤ final.heap.size := by rw [finalSize]; omega
  have stored : Stored clauses layout.directory layout.source final.heap :=
    Controller.Horn.NormalizeLoop.directory_frame layout represented growing (by
      intro cell lower upper
      have recordBelow := layout.headersBefore layout.recordHeader (by simp)
      exact lowFrame cell (by omega) (by omega))
  have recordDifferent : layout.recordHeader ≠ layout.directoryHeader ∧
      layout.recordHeader ≠ layout.endHeader := by
    have absent := (List.nodup_cons.mp layout.headersDistinct).1
    constructor
    · intro equal
      apply absent
      rw [equal]
      simp
    · intro equal
      apply absent
      rw [equal]
      simp
  have directoryHeld := Controller.Horn.JoinedNormalizeRow.cursor_of_option_frame
    directoryCursor growing (lowFrame layout.directoryHeader directoryCursor.bound recordDifferent.1.symm)
  have endHeld := Controller.Horn.JoinedNormalizeRow.cursor_of_option_frame
    directoryEnd growing (lowFrame layout.endHeader directoryEnd.bound recordDifferent.2.symm)
  have zeroFinal : final.reg 2 = word width 0 :=
    (endpointRegisters 2 (by decide) (by decide)).trans headerZero
  have oneFinal : final.reg 5 = word width 1 :=
    (endpointRegisters 5 (by decide) (by decide)).trans headerOne
  have maskFinal : final.reg 6 = word width (2 ^ width - 1) :=
    (endpointRegisters 6 (by decide) (by decide)).trans headerMask
  have initialMarks := Controller.Horn.NormalizeInitialize.scratch_marks state.heap n
  have row := scratch_header_row
    (state.heap ++ Array.replicate (5 * n + 4) (word width 0)) state.heap.size
    (Controller.Horn.Worklist.IndexedNormalize.Marks.initial n) initialMarks
    (by simp only [Array.size_append, Array.size_replicate]; omega)
  have recordBound : layout.recordHeader <
      (scratchHeaderHeap (state.heap ++ Array.replicate (5 * n + 4) (word width 0))
        state.heap.size n).size := by
    simp only [scratchHeaderHeap_size, Array.size_append, Array.size_replicate]
    omega
  have rowFinal : Controller.Horn.LiteralDispatch.RowStored
      (Controller.Horn.Worklist.IndexedNormalize.Row.empty
        (Controller.Horn.Worklist.IndexedNormalize.Marks.initial n)) layout.base
      (layout.base + 3 * n + 4) (layout.base + 4 * n + 4) (layout.base + 5 * n + 4) final.heap := by
    rw [baseEq, finalHeap]
    simpa only [Array.setIfInBounds_def, dite_eq_left recordBound] using
      Controller.Horn.RowScan.rowStored_after_input_store row layout.recordHeader recordBound
        (word width (state.heap.size + 5 * n + 4)) recordBefore
  have recordCursor : CursorStored final.heap.size layout.recordHeader final.heap := by
    have bound : layout.recordHeader < final.heap.size := by rw [finalSize]; omega
    refine ⟨bound, ?_⟩
    have actual : final.heap[layout.recordHeader]? = some (word width final.heap.size) := by
      rw [finalSize, finalHeap, Array.getElem?_setIfInBounds_self_of_lt recordBound]
    rw [Array.getElem?_eq_getElem bound] at actual
    exact Option.some.inj actual
  have invariant : Controller.Horn.NormalizeLoop.Invariant clauses layout
      (state.heap.size + 5 * n + 4) 0
      (Controller.Horn.Worklist.IndexedNormalize.Marks.initial n) final := by
    refine ⟨⟨stored, by omega, ?_, endHeld, zeroFinal, oneFinal, maskFinal, endpointRunning⟩,
      ⟨by omega, ?_, ?_⟩, recordCursor, ?_, rowFinal, ?_⟩
    · simpa only [Nat.mul_zero, Nat.add_zero] using directoryHeld
    · simp only [Controller.Horn.NormalizeLoop.recordOffset, List.take_zero, List.map_nil,
        List.sum_nil, Nat.add_zero]
      exact finalSize
    · intro index
      exact Fin.elim0 index
    · rw [baseEq]
    · exact Controller.Horn.Worklist.IndexedNormalize.Row.empty_correct _
        (Controller.Horn.Worklist.IndexedNormalize.Marks.initial_clean n)
  refine ⟨final, joined, invariant, ?_, endpointStack,
    endpointOutput.trans (headerOutput.trans allocatedOutput), ?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using endpointPC
  · intro cell before
    exact lowFrame cell (by omega) (by omega)
  · have headerCount : headered.reg 4 = word width n := by
      simpa [headered, scratchHeaderState, scratchHeaderConfiguration] using allocatedCount
    exact (endpointRegisters 4 (by decide) (by decide)).trans headerCount

  · have headerBase : headered.reg 3 = word width state.heap.size := by
      simpa [headered, scratchHeaderState, scratchHeaderConfiguration] using allocatedBase
    exact (endpointRegisters 3 (by decide) (by decide)).trans headerBase

/-- The allocator's actual local count is retained below the physical keep
and inverse-base words before entering the backend. Cleanup leaves the
inverse/count pair available for touched-dictionary reset. -/
def saveResetCountCode : Array (Instruction width 8) :=
  #[.pop 0, .pop 1, .push 4, .push 1, .push 0]

@[simp] theorem saveResetCountCode_size : (saveResetCountCode (width := width)).size = 5 := rfl

theorem save_reset_count_execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (keep inverse count : Word width) (rest : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (stackHeld : state.stack = keep :: inverse :: rest) (countHeld : state.reg 4 = count)
    (capacity : entry + 5 < 2 ^ width)
    (present : ∀ phase : Fin 5, program[entry + phase.val]? =
      (saveResetCountCode (width := width))[phase.val]?) :
    ∃ final, Execution program state final 5 (state.liveWords + 1) ∧
      final.heap = state.heap ∧ final.stack = keep :: inverse :: count :: rest ∧
      final.output = state.output ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → final.reg register = state.reg register) ∧
      final.pc = word width (entry + 5) ∧ final.halted = false := by
  let one := { state.advance.put 0 keep with stack := inverse :: rest }
  let two := { one.advance.put 1 inverse with stack := rest }
  let three := { two.advance with stack := count :: rest }
  let four := { three.advance with stack := inverse :: count :: rest }
  let final := { four.advance with stack := keep :: inverse :: count :: rest }
  have pcFits (offset : Nat) (bound : offset ≤ 5) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have pcValue : state.pc.val = entry := by
    rw [position]
    exact Nat.mod_eq_of_lt (pcFits 0 (by decide))
  have p1 : one.pc = word width (entry + 1) := by
    simp only [one, State.advance, State.put, pcValue]
  have p2 : two.pc = word width (entry + 2) := by
    simp only [two, State.advance, State.put, p1,
      show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (pcFits 1 (by decide))]
  have p3 : three.pc = word width (entry + 3) := by
    simp only [three, State.advance, p2,
      show (word width (entry + 2)).val = entry + 2 from Nat.mod_eq_of_lt (pcFits 2 (by decide))]
  have p4 : four.pc = word width (entry + 4) := by
    simp only [four, State.advance, p3,
      show (word width (entry + 3)).val = entry + 3 from Nat.mod_eq_of_lt (pcFits 3 (by decide))]
  have p5 : final.pc = word width (entry + 5) := by
    simp only [final, State.advance, p4,
      show (word width (entry + 4)).val = entry + 4 from Nat.mod_eq_of_lt (pcFits 4 (by decide))]
  have t0 : programStep program state = some one := by
    rw [fetched8 program state entry (.pop 0) position (pcFits 0 (by decide))
      (by simpa [saveResetCountCode] using present ⟨0, by decide⟩)]
    simp only [step, running, Bool.false_eq_true, ite_false, stackHeld]
    rfl
  have t1 : programStep program one = some two := by
    rw [fetched8 program one (entry + 1) (.pop 1) p1 (pcFits 1 (by decide))
      (by simpa [saveResetCountCode] using present ⟨1, by decide⟩)]
    simp [step, one, two, State.advance, State.put, running]
  have t2 : programStep program two = some three := by
    rw [fetched8 program two (entry + 2) (.push 4) p2 (pcFits 2 (by decide))
      (by simpa [saveResetCountCode] using present ⟨2, by decide⟩)]
    simp [step, three, two, one, State.advance, State.put, running, countHeld]
  have t3 : programStep program three = some four := by
    rw [fetched8 program three (entry + 3) (.push 1) p3 (pcFits 3 (by decide))
      (by simpa [saveResetCountCode] using present ⟨3, by decide⟩)]
    simp [step, four, three, two, one, State.advance, State.put, running]
  have t4 : programStep program four = some final := by
    rw [fetched8 program four (entry + 4) (.push 0) p4 (pcFits 4 (by decide))
      (by simpa [saveResetCountCode] using present ⟨4, by decide⟩)]
    simp [step, final, four, three, two, one, State.advance, State.put, running]
  have live1 : one.liveWords + 1 = state.liveWords := by
    simp only [one, State.advance, State.put, State.liveWords, stackHeld, List.length_cons]
    omega
  have live2 : two.liveWords + 2 = state.liveWords := by
    simp only [two, one, State.advance, State.put, State.liveWords, stackHeld, List.length_cons]
    omega
  have live3 : three.liveWords + 1 = state.liveWords := by
    simp only [three, two, one, State.advance, State.put, State.liveWords, stackHeld, List.length_cons]
    omega
  have live4 : four.liveWords = state.liveWords := by
    simp only [four, three, two, one, State.advance, State.put, State.liveWords, stackHeld, List.length_cons]
  have live5 : final.liveWords = state.liveWords + 1 := by
    simp only [final, four, three, two, one, State.advance, State.put, State.liveWords, stackHeld, List.length_cons]
    omega
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, p5, ?_⟩
  · have first := Execution.cons t0 (Execution.cons t1 (Execution.refl two))
    have second := Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.refl final)))
    convert first.append second using 1 <;>
      simp only [live4, live5]
    all_goals omega
  · intro register r0 r1
    simp only [final, four, three, two, one, State.advance, State.put, ite_eq_right r0, ite_eq_right r1]
  · exact running

/-- One scratch preparation and one physical saved-count phase provide the
hot normalizer state and the exact later cleanup/reset stack. The count comes
from the executed allocator register, not a reset caller premise. -/
theorem scratch_saved_execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (clauses : List (Clause (Fin n)))
    (layout : Controller.Horn.SourceDirectory.Layout clauses)
    (represented : Stored clauses layout.directory layout.source state.heap)
    (directoryCursor : CursorStored layout.directory layout.directoryHeader state.heap)
    (directoryEnd : CursorStored (layout.directory + 2 * clauses.length) layout.endHeader state.heap)
    (baseEq : layout.base = state.heap.size)
    (position : state.pc = word width entry) (running : state.halted = false)
    (localCount : state.reg 2 = word width n) (pointer : state.reg 1 = word width state.heap.size)
    (inverse : Nat) (rest : List (Word width))
    (saved : state.stack = word width inverse :: word width layout.recordHeader :: rest)
    (capacity : entry + 41 < 2 ^ width) (room : state.heap.size + 5 * n + 4 < 2 ^ width)
    (countAt : ∀ phase : Fin 11, program[entry + phase.val]? = (scratchCountCode width)[phase.val]?)
    (allocateAt : Controller.Horn.TrackedAllocate.CodeAt program (entry + 11))
    (headersAt : ∀ phase : Fin 15, program[entry + 16 + phase.val]? = (scratchHeaderCode width)[phase.val]?)
    (endpointAt : ∀ phase : Fin 5, program[entry + 31 + phase.val]? =
      (scratchEndpointCode (width := width))[phase.val]?)
    (saveCountAt : ∀ phase : Fin 5, program[entry + 36 + phase.val]? =
      (saveResetCountCode (width := width))[phase.val]?) :
    ∃ final : State width 8,
      Execution program state final (25 * n + 57) (state.liveWords + 5 * n + 5) ∧
      Controller.Horn.NormalizeLoop.Invariant clauses layout (state.heap.size + 5 * n + 4)
        0 (Controller.Horn.Worklist.IndexedNormalize.Marks.initial n) final ∧
      final.pc = word width (entry + 41) ∧
      final.stack = word width layout.recordHeader :: word width inverse :: word width n :: rest ∧
      final.output = state.output ∧
      (∀ cell, cell < layout.recordHeader → final.heap[cell]? = state.heap[cell]?) := by
  obtain ⟨ready, preparation, invariant, readyPC, readyStack, readyOutput, readyFrame, readyCount, readyBase⟩ :=
    scratch_initial_execution program state entry clauses layout represented directoryCursor directoryEnd
      baseEq position running localCount pointer inverse rest saved (by omega) room
      countAt allocateAt headersAt endpointAt
  obtain ⟨final, countTrace, finalHeap, finalStack, finalOutput, registers, finalPC, finalRunning⟩ :=
    save_reset_count_execution program ready (entry + 36) (word width layout.recordHeader)
      (word width inverse) (word width n) rest readyPC invariant.input.running
      readyStack readyCount (by omega) saveCountAt
  have readySize : ready.heap.size = state.heap.size + 5 * n + 4 := by
    simpa only [Controller.Horn.NormalizeLoop.recordOffset, List.take_zero, List.map_nil,
      List.sum_nil, Nat.add_zero] using invariant.records.endpoint
  have readyLive : ready.liveWords = state.liveWords + 5 * n + 4 := by
    unfold State.liveWords
    rw [readySize, readyStack, readyOutput, saved]
    simp only [List.length_cons]
    omega
  have finalInvariant : Controller.Horn.NormalizeLoop.Invariant clauses layout
      (state.heap.size + 5 * n + 4) 0
      (Controller.Horn.Worklist.IndexedNormalize.Marks.initial n) final := by
    refine ⟨⟨?_, invariant.input.indexBound, ?_, ?_, ?_, ?_, ?_, finalRunning⟩,
      ?_, ?_, invariant.recordsAbove, ?_, invariant.clean⟩
    · simpa only [finalHeap] using invariant.input.represented
    · simpa only [finalHeap] using invariant.input.cursor
    · simpa only [finalHeap] using invariant.input.endpoint
    · exact (registers 2 (by decide) (by decide)).trans invariant.input.zero
    · exact (registers 5 (by decide) (by decide)).trans invariant.input.one
    · exact (registers 6 (by decide) (by decide)).trans invariant.input.decrement
    · simpa only [finalHeap] using invariant.records
    · simpa only [finalHeap] using invariant.recordCursor
    · simpa only [finalHeap] using invariant.scratch
  refine ⟨final, ?_, finalInvariant, ?_, finalStack, finalOutput.trans readyOutput, ?_⟩
  · convert preparation.append countTrace using 1 <;> (try rw [readyLive])
    all_goals omega
  · simpa only [Nat.add_assoc] using finalPC
  · intro cell bound
    rw [finalHeap]
    exact readyFrame cell bound

private theorem pairHeap_prefix (heap : Array (Word width)) (labels : List Nat)
    (cell : Nat) (bound : cell < heap.size) :
    (ForestZeroPositive.pairHeap heap labels)[cell]? = heap[cell]? := by
  exact ForestZeroAdmissible.pairHeap_prefix heap labels cell bound

private theorem active_directory_cell (heap : Array (Word width))
    (protectedEnd sourceEnd directoryEnd : Nat) :
    (activeHeap heap protectedEnd (protectedEnd + 4) sourceEnd directoryEnd)[protectedEnd + 3]? = heap[protectedEnd + 3]? := by
  unfold activeHeap
  rw [Array.getElem?_setIfInBounds_ne (by omega),
    Array.getElem?_setIfInBounds_ne (by omega)]

/-- The two normalizer cursors come from physically emitted control cells.
Only the optional row's directory endpoint changes across the dispatch. -/
theorem constructor_header_cells (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient)
    (represented : Represented heap layout state)
    (references : List (List (Reference ambient))) (channels scratch : Nat) :
    let refs := reservedReferences references
    let compiled := (compileRows state (ForestZeroAssembly.originalRows refs)).1
    let prepared := ForestZeroQueryCaller.queryHeap heap layout state refs scratch
    let result := ForestZeroNonempty.search compiled (compiled.coordinates.size + 1) channels 0
    let covered := result.reason = .covered
    let slot := heap.size + 5 + 2 * references.length
    let installed := boundaryHeap
      (ForestZeroPositive.pairHeap prepared (ForestZeroPositive.channelLabels compiled channels))
      slot prepared.size (prepared.size + 2 * channels)
    let final := if covered then
      activeHeap installed heap.size (heap.size + 4) (prepared.size + 2 * channels) (slot + 2)
      else activeHeap prepared heap.size (heap.size + 4) prepared.size slot
    final[heap.size + 3]? = some (word width (heap.size + 5)) ∧
    final[heap.size + 4]? =
      some (word width (heap.size + 5 + 2 *
        (if covered then references.length + 1 else references.length))) := by
  let refs := reservedReferences references
  let compiled := (compileRows state (ForestZeroAssembly.originalRows refs)).1
  let prepared := ForestZeroQueryCaller.queryHeap heap layout state refs scratch
  let result := ForestZeroNonempty.search compiled (compiled.coordinates.size + 1) channels 0
  let slot := heap.size + 5 + 2 * references.length
  let pairs := ForestZeroPositive.pairHeap prepared (ForestZeroPositive.channelLabels compiled channels)
  let installed := boundaryHeap pairs slot prepared.size (prepared.size + 2 * channels)
  have preparedSize : prepared.size =
      heap.size + 5 + 2 * (references.length + 1) + 2 * references.flatten.length := by
    simp only [prepared, refs, ForestZeroQueryCaller.queryHeap_size,
      reservedReferences_length, reservedReferences_flatten]
  have directory : prepared[heap.size + 3]? = some (word width (heap.size + 5)) := by
    simpa only [prepared, ForestZeroQueryCaller.headerValues,
      List.getElem_cons_zero, List.getElem_cons_succ] using
      ForestZeroQueryCaller.query_header_cell heap layout state represented refs scratch 3
        (by decide) (by decide)
  have installedDirectory : installed[heap.size + 3]? = prepared[heap.size + 3]? := by
    exact (boundary_prefix pairs slot prepared.size (prepared.size + 2 * channels)
      (heap.size + 3) (by dsimp only [slot]; omega)).trans
      (pairHeap_prefix prepared _ (heap.size + 3) (by rw [preparedSize]; omega))
  change (if result.reason = .covered then
    activeHeap installed heap.size (heap.size + 4) (prepared.size + 2 * channels) (slot + 2)
    else activeHeap prepared heap.size (heap.size + 4) prepared.size slot)[heap.size + 3]? =
      some (word width (heap.size + 5)) ∧
    (if result.reason = .covered then
      activeHeap installed heap.size (heap.size + 4) (prepared.size + 2 * channels) (slot + 2)
      else activeHeap prepared heap.size (heap.size + 4) prepared.size slot)[heap.size + 4]? =
      some (word width (heap.size + 5 + 2 *
        (if result.reason = .covered then references.length + 1 else references.length)))
  by_cases covered : result.reason = .covered
  · rw [ite_eq_left covered]
    constructor
    · exact (active_directory_cell installed heap.size _ _).trans
        (installedDirectory.trans directory)
    · have cells := (active_cells installed heap.size (heap.size + 4)
        (prepared.size + 2 * channels) (slot + 2)
        (by simp only [installed, boundaryHeap_size, pairs, ForestZeroPositive.pairHeap_size];
            rw [preparedSize]; omega)
        (by simp only [installed, boundaryHeap_size, pairs, ForestZeroPositive.pairHeap_size];
            rw [preparedSize]; omega) (by omega)).2
      have endpoint : slot + 2 = heap.size + 5 + 2 * (references.length + 1) := by
        dsimp only [slot]
        omega
      simpa only [endpoint, ite_eq_left covered] using cells
  · rw [ite_eq_right covered]
    constructor
    · exact (active_directory_cell prepared heap.size _ _).trans directory
    · simpa only [ite_eq_right covered] using (active_cells prepared heap.size (heap.size + 4) prepared.size slot
        (by rw [preparedSize]; omega) (by rw [preparedSize]; omega) (by omega)).2

private theorem cursorStored_of_option {heap : Array (Word width)} {pointer header : Nat}
    (bound : header < heap.size) (cell : heap[header]? = some (word width pointer)) :
    CursorStored pointer header heap := by
  refine ⟨bound, ?_⟩
  simpa only [Array.getElem?_eq_getElem bound, Option.some.injEq] using cell

/-- Actual source emission supplies the complete hot-normalizer input pair.
The retained directory word and the dispatched end word are decoded on the
same heap that carries the finite source clauses. -/
theorem constructor_backend_inputs (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient)
    (represented : Represented heap layout state)
    (references : List (List (Reference ambient))) (channels scratch : Nat)
    (within : channels ≤ ambient) :
    let refs := reservedReferences references
    let compiled := (compileRows state (ForestZeroAssembly.originalRows refs)).1
    let prepared := ForestZeroQueryCaller.queryHeap heap layout state refs scratch
    let result := ForestZeroNonempty.search compiled (compiled.coordinates.size + 1) channels 0
    let covered := result.reason = .covered
    let slot := heap.size + 5 + 2 * references.length
    let installed := boundaryHeap
      (ForestZeroPositive.pairHeap prepared (ForestZeroPositive.channelLabels compiled channels))
      slot prepared.size (prepared.size + 2 * channels)
    let final := if covered then
      activeHeap installed heap.size (heap.size + 4) (prepared.size + 2 * channels) (slot + 2)
      else activeHeap prepared heap.size (heap.size + 4) prepared.size slot
    ∃ clauses : List (Clause (Fin compiled.coordinates.size)),
      ∃ backend : Controller.Horn.SourceDirectory.Layout clauses,
      Stored clauses backend.directory backend.source final ∧
      CursorStored backend.directory backend.directoryHeader final ∧
      CursorStored (backend.directory + 2 * clauses.length) backend.endHeader final ∧
      backend.base = final.size ∧ backend.recordHeader = heap.size ∧
      backend.inputHeader = heap.size + 1 ∧ backend.firstHeader = heap.size + 2 ∧
      backend.directoryHeader = heap.size + 3 ∧ backend.endHeader = heap.size + 4 := by
  let refs := reservedReferences references
  let compiled := (compileRows state (ForestZeroAssembly.originalRows refs)).1
  let prepared := ForestZeroQueryCaller.queryHeap heap layout state refs scratch
  let result := ForestZeroNonempty.search compiled (compiled.coordinates.size + 1) channels 0
  let covered := result.reason = .covered
  let slot := heap.size + 5 + 2 * references.length
  let installed := boundaryHeap
    (ForestZeroPositive.pairHeap prepared (ForestZeroPositive.channelLabels compiled channels))
    slot prepared.size (prepared.size + 2 * channels)
  let final := if covered then
    activeHeap installed heap.size (heap.size + 4) (prepared.size + 2 * channels) (slot + 2)
    else activeHeap prepared heap.size (heap.size + 4) prepared.size slot
  change ∃ clauses : List (Clause (Fin compiled.coordinates.size)),
    ∃ backend : Controller.Horn.SourceDirectory.Layout clauses,
    Stored clauses backend.directory backend.source final ∧
    CursorStored backend.directory backend.directoryHeader final ∧
    CursorStored (backend.directory + 2 * clauses.length) backend.endHeader final ∧
    backend.base = final.size ∧ backend.recordHeader = heap.size ∧
    backend.inputHeader = heap.size + 1 ∧ backend.firstHeader = heap.size + 2 ∧
    backend.directoryHeader = heap.size + 3 ∧ backend.endHeader = heap.size + 4
  obtain ⟨clauses, stored, rowCount, sourceEnd, backend,
      directoryEq, sourceEq, baseEq, recordEq, inputEq, firstEq, directoryHeaderEq, endHeaderEq⟩ :=
    constructor_backend_stored heap layout state represented references channels scratch within
  have actualHeaders := constructor_header_cells heap layout state represented references channels scratch
  have preparedSize : prepared.size =
      heap.size + 5 + 2 * (references.length + 1) + 2 * references.flatten.length := by
    simp only [prepared, refs, ForestZeroQueryCaller.queryHeap_size,
      reservedReferences_length, reservedReferences_flatten]
  have growing : prepared.size ≤ final.size := by
    dsimp only [final]
    split
    · simp only [installed, activeHeap_size, boundaryHeap_size,
        ForestZeroPositive.pairHeap_size]
      omega
    · simp only [activeHeap_size]
      exact le_rfl
  have dirBound : heap.size + 3 < final.size := by rw [preparedSize] at growing; omega
  have endBound : heap.size + 4 < final.size := by rw [preparedSize] at growing; omega
  refine ⟨clauses, backend, ?_, ?_, ?_, baseEq, recordEq, inputEq, firstEq,
    directoryHeaderEq, endHeaderEq⟩
  · rw [directoryEq, sourceEq]
    exact stored
  · rw [directoryEq, directoryHeaderEq]
    exact cursorStored_of_option dirBound actualHeaders.1
  · rw [directoryEq, endHeaderEq, rowCount]
    exact cursorStored_of_option endBound actualHeaders.2


/-- A local fetched block is preserved by the normalizer proof mask when the
fixed block itself contains no caller stack or output instruction. -/
private theorem neutral_block_fetch (program block : Program width 8)
    (position index : Nat)
    (present : program[position]? = block[index]?)
    (identity : Controller.Cost.ForestZeroNormalizeFrame.neutralProgram block = block) :
    (Controller.Cost.ForestZeroNormalizeFrame.neutralProgram program)[position]? = block[index]? := by
  rw [Controller.Cost.ForestZeroNormalizeFrame.neutralProgram, Array.getElem?_map, present]
  have cells := congrArg (fun actual : Program width 8 => actual[index]?) identity
  simpa only [Controller.Cost.ForestZeroNormalizeFrame.neutralProgram,
    Array.getElem?_map] using cells

private theorem neutral_fetch_from_block (program block : Program width 8)
    (position index : Nat) (bound : index < block.size)
    (found : program[position]? = some (block[index]'bound))
    (identity : Controller.Cost.ForestZeroNormalizeFrame.neutralProgram block = block) :
    (Controller.Cost.ForestZeroNormalizeFrame.neutralProgram program)[position]? =
      some (block[index]'bound) := by
  have element : block[index]? = some (block[index]'bound) :=
    Array.getElem?_eq_getElem bound
  exact (neutral_block_fetch program block position index
    (found.trans element.symm) identity).trans element

private theorem neutral_fixed_identity (block : Program width 8)
    (every : ∀ instruction ∈ block, Controller.Horn.SourceDirectory.CallerNeutral instruction) :
    Controller.Cost.ForestZeroNormalizeFrame.neutralProgram block = block := by
  unfold Controller.Cost.ForestZeroNormalizeFrame.neutralProgram
  calc
    block.map Controller.Cost.ForestZeroNormalizeFrame.neutralInstruction =
        block.map (fun instruction => instruction) := by
      apply Array.map_congr_left
      intro instruction member
      have allowed := every instruction member
      cases instruction <;> first | rfl | contradiction
    _ = block := Array.map_id' block

private theorem neutral_directory_code (width directoryHeader endHeader inputHeader firstHeader exit : Nat) :
    Controller.Cost.ForestZeroNormalizeFrame.neutralProgram (Controller.Horn.ClauseEntry.code width directoryHeader endHeader inputHeader firstHeader exit) =
      Controller.Horn.ClauseEntry.code width directoryHeader endHeader inputHeader firstHeader exit := by
  apply neutral_fixed_identity
  simp [Controller.Horn.ClauseEntry.code, Controller.Horn.SourceDirectory.CallerNeutral,
    Array.mem_def, -Array.mem_toList_iff]

private theorem neutral_row_code (width entry n base cursorHeader startHeader exit : Nat) :
    Controller.Cost.ForestZeroNormalizeFrame.neutralProgram (Controller.Horn.RowScan.rowCode width entry n base cursorHeader startHeader exit) =
      Controller.Horn.RowScan.rowCode width entry n base cursorHeader startHeader exit := by
  apply neutral_fixed_identity
  simp only [Controller.Horn.RowScan.rowCode, Array.forall_mem_append]
  repeat' apply And.intro
  all_goals simp [Controller.Horn.RowScan.testCode, Controller.Horn.SourceScan.pairCode,
    Controller.Horn.RowScan.readMarksCode, Controller.Horn.RowScan.dispatchCode,
    Controller.Horn.RowScan.writeMarkCode, Controller.Horn.NormalizeProgram.literalCode,
    Controller.Horn.SourceDirectory.CallerNeutral, Array.mem_def, -Array.mem_toList_iff]

private theorem neutral_dispatch_code (width n entry base exit : Nat) :
    Controller.Cost.ForestZeroNormalizeFrame.neutralProgram (Controller.Horn.RuleDispatch.code width n entry base exit) =
      Controller.Horn.RuleDispatch.code width n entry base exit := by
  apply neutral_fixed_identity
  simp [Controller.Horn.RuleDispatch.code, Controller.Horn.SourceDirectory.CallerNeutral,
    Array.mem_def, -Array.mem_toList_iff]

private theorem neutral_address_code (width cursorHeader : Nat) :
    Controller.Cost.ForestZeroNormalizeFrame.neutralProgram (Controller.Horn.RuleCopy.recordAddressCode width cursorHeader) =
      Controller.Horn.RuleCopy.recordAddressCode width cursorHeader := by
  apply neutral_fixed_identity
  simp [Controller.Horn.RuleCopy.recordAddressCode, Controller.Horn.SourceDirectory.CallerNeutral,
    Array.mem_def, -Array.mem_toList_iff]

private theorem neutral_header_code (width  : Nat) :
    Controller.Cost.ForestZeroNormalizeFrame.neutralProgram (Controller.Horn.RuleCopy.headerCode width) =
      Controller.Horn.RuleCopy.headerCode width := by
  apply neutral_fixed_identity
  simp [Controller.Horn.RuleCopy.headerCode, Controller.Horn.SourceDirectory.CallerNeutral,
    Array.mem_def, -Array.mem_toList_iff]

private theorem neutral_copySetup_code (width positiveHeader : Nat) :
    Controller.Cost.ForestZeroNormalizeFrame.neutralProgram (Controller.Horn.RuleCopy.setupCode width positiveHeader) =
      Controller.Horn.RuleCopy.setupCode width positiveHeader := by
  apply neutral_fixed_identity
  simp [Controller.Horn.RuleCopy.setupCode, Controller.Horn.SourceDirectory.CallerNeutral,
    Array.mem_def, -Array.mem_toList_iff]

private theorem neutral_body_code (width entry sourceEnd exit : Nat) :
    Controller.Cost.ForestZeroNormalizeFrame.neutralProgram (Controller.Horn.RuleCopy.bodyCode width entry sourceEnd exit) =
      Controller.Horn.RuleCopy.bodyCode width entry sourceEnd exit := by
  apply neutral_fixed_identity
  simp [Controller.Horn.RuleCopy.bodyCode, Controller.Horn.SourceDirectory.CallerNeutral,
    Array.mem_def, -Array.mem_toList_iff]

private theorem neutral_cursor_code (width cursorHeader : Nat) :
    Controller.Cost.ForestZeroNormalizeFrame.neutralProgram (Controller.Horn.RuleCopy.cursorUpdateCode width cursorHeader) =
      Controller.Horn.RuleCopy.cursorUpdateCode width cursorHeader := by
  apply neutral_fixed_identity
  simp [Controller.Horn.RuleCopy.cursorUpdateCode, Controller.Horn.SourceDirectory.CallerNeutral,
    Array.mem_def, -Array.mem_toList_iff]

private theorem neutral_reset_code (width entry limit : Nat) :
    Controller.Cost.ForestZeroNormalizeFrame.neutralProgram (Controller.Horn.ResetPointer.code width entry limit) =
      Controller.Horn.ResetPointer.code width entry limit := by
  apply neutral_fixed_identity
  simp [Controller.Horn.ResetPointer.code, Controller.Horn.SourceDirectory.CallerNeutral,
    Array.mem_def, -Array.mem_toList_iff]

private theorem neutral_resetSetup_code (width header base : Nat) :
    Controller.Cost.ForestZeroNormalizeFrame.neutralProgram (Controller.Horn.ResetPointer.setupCode width header base) =
      Controller.Horn.ResetPointer.setupCode width header base := by
  apply neutral_fixed_identity
  simp [Controller.Horn.ResetPointer.setupCode, Controller.Horn.SourceDirectory.CallerNeutral,
    Array.mem_def, -Array.mem_toList_iff]

private theorem neutral_resetHeader_code (width n base : Nat) :
    Controller.Cost.ForestZeroNormalizeFrame.neutralProgram (Controller.Horn.ResetReuse.headerCode width n base) =
      Controller.Horn.ResetReuse.headerCode width n base := by
  apply neutral_fixed_identity
  simp [Controller.Horn.ResetReuse.headerCode, Controller.Horn.SourceDirectory.CallerNeutral,
    Array.mem_def, -Array.mem_toList_iff]

/-- Only the seven fixed normalizer blocks must be neutral. Caller stack,
output and cleanup instructions elsewhere in the same program are unrestricted. -/
theorem normalizer_local_code (program : Program width 8) (entry : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (layout : Controller.Horn.SourceDirectory.Layout clauses)
    (present : Controller.Horn.NormalizeLoop.CodeAt program entry clauses layout) :
    Controller.Horn.NormalizeLoop.CodeAt
      (Controller.Cost.ForestZeroNormalizeFrame.neutralProgram program) entry clauses layout := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro phase
    exact neutral_fetch_from_block program
      (Controller.Horn.ClauseEntry.code width layout.directoryHeader layout.endHeader
        layout.inputHeader layout.firstHeader (entry + 161)) _ phase.val _
      (present.directory phase) (neutral_directory_code _ _ _ _ _ _)
  · intro phase
    exact neutral_fetch_from_block program
      (Controller.Horn.RowScan.rowCode width (entry + 16) n layout.base layout.inputHeader
        layout.firstHeader (entry + 93)) _ phase.val _
      (present.row phase) (neutral_row_code _ _ _ _ _ _ _)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro phase
      exact neutral_fetch_from_block program
        (Controller.Horn.RuleDispatch.code width n (entry + 93) layout.base ((entry + 93) + 17))
        _ phase.val _ (present.copy.selection phase) (neutral_dispatch_code _ _ _ _ _)
    · intro phase
      exact neutral_fetch_from_block program
        (Controller.Horn.RuleCopy.recordAddressCode width layout.recordHeader)
        _ phase.val _ (present.copy.address phase) (neutral_address_code _ _)
    · intro phase
      exact neutral_fetch_from_block program (Controller.Horn.RuleCopy.headerCode width)
        _ phase.val _ (present.copy.header phase) (neutral_header_code _)
    · constructor
      · exact Controller.Cost.ForestZeroNormalizeFrame.neutral_fetch _ _ _ present.copy.bypass.1 trivial
      · exact Controller.Cost.ForestZeroNormalizeFrame.neutral_fetch _ _ _ present.copy.bypass.2 trivial
    · intro phase
      exact neutral_fetch_from_block program
        (Controller.Horn.RuleCopy.setupCode width (layout.base + 2 * n))
        _ phase.val _ (present.copy.setup phase) (neutral_copySetup_code _ _)
    · intro phase
      exact neutral_fetch_from_block program
        (Controller.Horn.RuleCopy.bodyCode width ((entry + 93) + 29)
          (layout.base + 3 * n + 4) ((entry + 93) + 37))
        _ phase.val _ (present.copy.body phase) (neutral_body_code _ _ _ _)
    · exact Controller.Cost.ForestZeroNormalizeFrame.neutral_fetch _ _ _ present.copy.finish trivial
    · intro phase
      exact neutral_fetch_from_block program
        (Controller.Horn.RuleCopy.cursorUpdateCode width layout.recordHeader)
        _ phase.val _ (present.copy.cursor phase) (neutral_cursor_code _ _)
  · intro phase
    exact neutral_fetch_from_block program
      (Controller.Horn.ResetPointer.setupCode width (layout.base + 2 * n + 2) layout.base)
      _ phase.val _ (present.setup phase) (neutral_resetSetup_code _ _ _)
  · intro phase
    exact neutral_fetch_from_block program
      (Controller.Horn.ResetPointer.code width (entry + 138) (layout.base + 5 * n + 4))
      _ phase.val _ (present.reset phase) (neutral_reset_code _ _ _)
  · intro phase
    exact neutral_fetch_from_block program
      (Controller.Horn.ResetReuse.headerCode width n layout.base)
      _ phase.val _ (present.headers phase) (neutral_resetHeader_code _ _ _)
  · exact Controller.Cost.ForestZeroNormalizeFrame.neutral_fetch _ _ _ present.returnBranch trivial

/-- Preserve the actual scratch base together with the allocator's local count
before the normalizer starts mutating the query record cursor header. -/
def saveProjectionCode : Array (Instruction width 8) :=
  #[.pop 0, .pop 1, .push 3, .push 4, .push 1, .push 0]

@[simp] theorem saveProjectionCode_size : (saveProjectionCode (width := width)).size = 6 := rfl

theorem save_projection_execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (keep inverse count base : Word width) (rest : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (stackHeld : state.stack = keep :: inverse :: rest)
    (countHeld : state.reg 4 = count) (baseHeld : state.reg 3 = base)
    (capacity : entry + 6 < 2 ^ width)
    (present : ∀ phase : Fin 6, program[entry + phase.val]? =
      (saveProjectionCode (width := width))[phase.val]?) :
    ∃ final, Execution program state final 6 (state.liveWords + 2) ∧
      final.heap = state.heap ∧ final.stack = keep :: inverse :: count :: base :: rest ∧
      final.output = state.output ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → final.reg register = state.reg register) ∧
      final.pc = word width (entry + 6) ∧ final.halted = false := by
  let one := { state.advance.put 0 keep with stack := inverse :: rest }
  let two := { one.advance.put 1 inverse with stack := rest }
  let three := { two.advance with stack := base :: rest }
  let four := { three.advance with stack := count :: base :: rest }
  let five := { four.advance with stack := inverse :: count :: base :: rest }
  let final := { five.advance with stack := keep :: inverse :: count :: base :: rest }
  have pcFits (offset : Nat) (bound : offset ≤ 6) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have p1 : one.pc = word width (entry + 1) := by
    simpa only [one, State.put] using advance8_pc state entry position (pcFits 0 (by decide))
  have p2 : two.pc = word width (entry + 2) := by
    simpa only [two, State.put, Nat.add_assoc] using advance8_pc one (entry + 1) p1 (pcFits 1 (by decide))
  have p3 : three.pc = word width (entry + 3) := by
    simpa only [three, Nat.add_assoc] using advance8_pc two (entry + 2) p2 (pcFits 2 (by decide))
  have p4 : four.pc = word width (entry + 4) := by
    simpa only [four, Nat.add_assoc] using advance8_pc three (entry + 3) p3 (pcFits 3 (by decide))
  have p5 : five.pc = word width (entry + 5) := by
    simpa only [five, Nat.add_assoc] using advance8_pc four (entry + 4) p4 (pcFits 4 (by decide))
  have p6 : final.pc = word width (entry + 6) := by
    simpa only [final, Nat.add_assoc] using advance8_pc five (entry + 5) p5 (pcFits 5 (by decide))
  have t0 : programStep program state = some one := by
    rw [fetched8 program state entry (.pop 0) position (pcFits 0 (by decide))
      (by simpa [saveProjectionCode] using present ⟨0, by decide⟩)]
    simp only [step, running, Bool.false_eq_true, ite_false, stackHeld]
    rfl
  have t1 : programStep program one = some two := by
    rw [fetched8 program one (entry + 1) (.pop 1) p1 (pcFits 1 (by decide))
      (by simpa [saveProjectionCode] using present ⟨1, by decide⟩)]
    simp [step, one, two, State.advance, State.put, running]
  have t2 : programStep program two = some three := by
    rw [fetched8 program two (entry + 2) (.push 3) p2 (pcFits 2 (by decide))
      (by simpa [saveProjectionCode] using present ⟨2, by decide⟩)]
    simp [step, three, two, one, State.advance, State.put, running, baseHeld]
  have t3 : programStep program three = some four := by
    rw [fetched8 program three (entry + 3) (.push 4) p3 (pcFits 3 (by decide))
      (by simpa [saveProjectionCode] using present ⟨3, by decide⟩)]
    simp [step, four, three, two, one, State.advance, State.put, running, countHeld]
  have t4 : programStep program four = some five := by
    rw [fetched8 program four (entry + 4) (.push 1) p4 (pcFits 4 (by decide))
      (by simpa [saveProjectionCode] using present ⟨4, by decide⟩)]
    simp [step, five, four, three, two, one, State.advance, State.put, running]
  have t5 : programStep program five = some final := by
    rw [fetched8 program five (entry + 5) (.push 0) p5 (pcFits 5 (by decide))
      (by simpa [saveProjectionCode] using present ⟨5, by decide⟩)]
    simp [step, final, five, four, three, two, one, State.advance, State.put, running]
  have live1 : one.liveWords + 1 = state.liveWords := by
    simp only [one, State.advance, State.put, State.liveWords, stackHeld, List.length_cons]
    omega
  have live2 : two.liveWords + 2 = state.liveWords := by
    simp only [two, one, State.advance, State.put, State.liveWords, stackHeld, List.length_cons]
    omega
  have live3 : three.liveWords + 1 = state.liveWords := by
    simp only [three, two, one, State.advance, State.put, State.liveWords, stackHeld, List.length_cons]
    omega
  have live4 : four.liveWords = state.liveWords := by
    simp only [four, three, two, one, State.advance, State.put, State.liveWords, stackHeld, List.length_cons]
  have live5 : five.liveWords = state.liveWords + 1 := by
    simp only [five, four, three, two, one, State.advance, State.put, State.liveWords, stackHeld, List.length_cons]
    omega
  have live6 : final.liveWords = state.liveWords + 2 := by
    simp only [final, five, four, three, two, one, State.advance, State.put, State.liveWords, stackHeld, List.length_cons]
    omega
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, p6, running⟩
  · have first := Execution.cons t0 (Execution.cons t1 (Execution.refl two))
    have second := Execution.cons t2 (Execution.cons t3 (Execution.cons t4
      (Execution.cons t5 (Execution.refl final))))
    convert first.append second using 1 <;> (try simp only [live4, live5, live6])
    all_goals omega
  · intro register r0 r1
    simp only [final, five, four, three, two, one, State.advance, State.put, ite_eq_right r0, ite_eq_right r1]

theorem scratch_projection_saved_execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (clauses : List (Clause (Fin n)))
    (layout : Controller.Horn.SourceDirectory.Layout clauses)
    (represented : Stored clauses layout.directory layout.source state.heap)
    (directoryCursor : CursorStored layout.directory layout.directoryHeader state.heap)
    (directoryEnd : CursorStored (layout.directory + 2 * clauses.length) layout.endHeader state.heap)
    (baseEq : layout.base = state.heap.size)
    (position : state.pc = word width entry) (running : state.halted = false)
    (localCount : state.reg 2 = word width n) (pointer : state.reg 1 = word width state.heap.size)
    (inverse : Nat) (rest : List (Word width))
    (saved : state.stack = word width inverse :: word width layout.recordHeader :: rest)
    (capacity : entry + 42 < 2 ^ width) (room : state.heap.size + 5 * n + 4 < 2 ^ width)
    (countAt : ∀ phase : Fin 11, program[entry + phase.val]? = (scratchCountCode width)[phase.val]?)
    (allocateAt : Controller.Horn.TrackedAllocate.CodeAt program (entry + 11))
    (headersAt : ∀ phase : Fin 15, program[entry + 16 + phase.val]? = (scratchHeaderCode width)[phase.val]?)
    (endpointAt : ∀ phase : Fin 5, program[entry + 31 + phase.val]? =
      (scratchEndpointCode (width := width))[phase.val]?)
    (saveCountAt : ∀ phase : Fin 6, program[entry + 36 + phase.val]? =
      (saveProjectionCode (width := width))[phase.val]?) :
    ∃ final : State width 8,
      Execution program state final (25 * n + 58) (state.liveWords + 5 * n + 6) ∧
      Controller.Horn.NormalizeLoop.Invariant clauses layout (state.heap.size + 5 * n + 4)
        0 (Controller.Horn.Worklist.IndexedNormalize.Marks.initial n) final ∧
      final.pc = word width (entry + 42) ∧
      final.stack = word width layout.recordHeader :: word width inverse :: word width n :: word width state.heap.size :: rest ∧
      final.output = state.output ∧
      (∀ cell, cell < layout.recordHeader → final.heap[cell]? = state.heap[cell]?) := by
  obtain ⟨ready, preparation, invariant, readyPC, readyStack, readyOutput, readyFrame, readyCount, readyBase⟩ :=
    scratch_initial_execution program state entry clauses layout represented directoryCursor directoryEnd
      baseEq position running localCount pointer inverse rest saved (by omega) room
      countAt allocateAt headersAt endpointAt
  obtain ⟨final, countTrace, finalHeap, finalStack, finalOutput, registers, finalPC, finalRunning⟩ :=
    save_projection_execution program ready (entry + 36) (word width layout.recordHeader)
      (word width inverse) (word width n) (word width state.heap.size) rest readyPC invariant.input.running
      readyStack readyCount readyBase (by omega) saveCountAt
  have readySize : ready.heap.size = state.heap.size + 5 * n + 4 := by
    simpa only [Controller.Horn.NormalizeLoop.recordOffset, List.take_zero, List.map_nil,
      List.sum_nil, Nat.add_zero] using invariant.records.endpoint
  have readyLive : ready.liveWords = state.liveWords + 5 * n + 4 := by
    unfold State.liveWords
    rw [readySize, readyStack, readyOutput, saved]
    simp only [List.length_cons]
    omega
  have finalInvariant : Controller.Horn.NormalizeLoop.Invariant clauses layout
      (state.heap.size + 5 * n + 4) 0
      (Controller.Horn.Worklist.IndexedNormalize.Marks.initial n) final := by
    refine ⟨⟨?_, invariant.input.indexBound, ?_, ?_, ?_, ?_, ?_, finalRunning⟩,
      ?_, ?_, invariant.recordsAbove, ?_, invariant.clean⟩
    · simpa only [finalHeap] using invariant.input.represented
    · simpa only [finalHeap] using invariant.input.cursor
    · simpa only [finalHeap] using invariant.input.endpoint
    · exact (registers 2 (by decide) (by decide)).trans invariant.input.zero
    · exact (registers 5 (by decide) (by decide)).trans invariant.input.one
    · exact (registers 6 (by decide) (by decide)).trans invariant.input.decrement
    · simpa only [finalHeap] using invariant.records
    · simpa only [finalHeap] using invariant.recordCursor
    · simpa only [finalHeap] using invariant.scratch
  refine ⟨final, ?_, finalInvariant, ?_, finalStack, finalOutput.trans readyOutput, ?_⟩
  · convert preparation.append countTrace using 1 <;> (try rw [readyLive])
    all_goals omega
  · simpa only [Nat.add_assoc] using finalPC
  · intro cell bound
    rw [finalHeap]
    exact readyFrame cell bound

/-- The local neutral mask gives one actual normalizer trace while retaining
both saved allocation words and the original caller output. -/
theorem normalizer_saved_execution (prefixSize : Nat) (program : Program width 8) (entry : Nat)
    (clauses : List (Clause (Fin n))) (layout : Controller.Horn.SourceDirectory.Layout clauses)
    (present : Controller.Horn.NormalizeLoop.CodeAt program entry clauses layout)
    (recordStart : Nat) (marks : Controller.Horn.Worklist.IndexedNormalize.Marks n)
    (state : State width 8)
    (invariant : Controller.Horn.NormalizeLoop.Invariant clauses layout recordStart 0 marks state)
    (dual : ∀ index : Fin clauses.length, Controller.Horn.DualHornClause clauses[index.val])
    (position : state.pc = word width entry) (capacity : entry + 161 < 2 ^ width)
    (room : state.heap.size + 3 * clauses.length + (clauses.map List.length).sum < 2 ^ width)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBase : prefixSize ≤ layout.base)
    (headersAbove : ∀ header ∈ [layout.recordHeader, layout.inputHeader, layout.firstHeader,
      layout.directoryHeader, layout.endHeader], prefixSize ≤ header) :
    ∃ final finalMarks ticks peak,
      Execution program state final ticks peak ∧
      Controller.Horn.NormalizeLoop.Invariant clauses layout recordStart clauses.length finalMarks final ∧
      final.pc = word width (entry + 161) ∧
      ticks ≤ 61 * (clauses.map List.length).sum + 71 * clauses.length + 6 ∧
      peak ≤ state.liveWords + 3 * clauses.length + (clauses.map List.length).sum ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame prefixSize state.heap final.heap ∧
      final.stack = state.stack ∧ final.output = state.output := by
  obtain ⟨final, finalMarks, ticks, peak, run, complete, finalPC, timeBound, spaceBound, frame⟩ :=
    Controller.Cost.ForestZeroNormalizeFrame.all_execution prefixSize
      (Controller.Cost.ForestZeroNormalizeFrame.neutralProgram program) entry clauses layout
      (normalizer_local_code program entry clauses layout present) recordStart marks state invariant
      dual position capacity room (Controller.Cost.ForestZeroNormalizeFrame.neutral_program program)
      prefixBound prefixBase headersAbove
  have kept := Controller.Horn.SourceDirectory.caller_execution
    (Controller.Cost.ForestZeroNormalizeFrame.neutral_program program) run
  refine ⟨final, finalMarks, ticks, peak,
    Controller.Cost.ForestZeroNormalizeFrame.neutral_execution run complete.input.running,
    complete, finalPC, timeBound, by omega, frame, kept.1, kept.2⟩

theorem scratch_normalized_execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (clauses : List (Clause (Fin n)))
    (layout : Controller.Horn.SourceDirectory.Layout clauses)
    (represented : Stored clauses layout.directory layout.source state.heap)
    (directoryCursor : CursorStored layout.directory layout.directoryHeader state.heap)
    (directoryEnd : CursorStored (layout.directory + 2 * clauses.length) layout.endHeader state.heap)
    (baseEq : layout.base = state.heap.size)
    (position : state.pc = word width entry) (running : state.halted = false)
    (localCount : state.reg 2 = word width n) (pointer : state.reg 1 = word width state.heap.size)
    (inverse : Nat) (rest : List (Word width))
    (saved : state.stack = word width inverse :: word width layout.recordHeader :: rest)
    (capacity : entry + 203 < 2 ^ width)
    (room : state.heap.size + 5 * n + 4 + 3 * clauses.length + (clauses.map List.length).sum < 2 ^ width)
    (countAt : ∀ phase : Fin 11, program[entry + phase.val]? = (scratchCountCode width)[phase.val]?)
    (allocateAt : Controller.Horn.TrackedAllocate.CodeAt program (entry + 11))
    (headersAt : ∀ phase : Fin 15, program[entry + 16 + phase.val]? = (scratchHeaderCode width)[phase.val]?)
    (endpointAt : ∀ phase : Fin 5, program[entry + 31 + phase.val]? =
      (scratchEndpointCode (width := width))[phase.val]?)
    (saveCountAt : ∀ phase : Fin 6, program[entry + 36 + phase.val]? =
      (saveProjectionCode (width := width))[phase.val]?)
    (normalizerAt : Controller.Horn.NormalizeLoop.CodeAt program (entry + 42) clauses layout)
    (dual : ∀ index : Fin clauses.length, Controller.Horn.DualHornClause clauses[index.val])
    (headersAbove : ∀ header ∈ [layout.recordHeader, layout.inputHeader, layout.firstHeader,
      layout.directoryHeader, layout.endHeader], layout.recordHeader ≤ header) :
    ∃ final finalMarks ticks peak,
      Execution program state final ticks peak ∧
      Controller.Horn.NormalizeLoop.Invariant clauses layout (state.heap.size + 5 * n + 4)
        clauses.length finalMarks final ∧
      final.pc = word width (entry + 203) ∧
      ticks ≤ 25 * n + 61 * (clauses.map List.length).sum + 71 * clauses.length + 64 ∧
      peak ≤ state.liveWords + 5 * n + 6 + 3 * clauses.length + (clauses.map List.length).sum ∧
      final.stack = word width layout.recordHeader :: word width inverse :: word width n ::
        word width state.heap.size :: rest ∧
      final.output = state.output ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.recordHeader state.heap final.heap := by
  obtain ⟨ready, prepare, initial, readyPC, readyStack, readyOutput, readyCells⟩ :=
    scratch_projection_saved_execution program state entry clauses layout represented directoryCursor
      directoryEnd baseEq position running localCount pointer inverse rest saved (by omega) (by omega)
      countAt allocateAt headersAt endpointAt saveCountAt
  have readySize : ready.heap.size = state.heap.size + 5 * n + 4 := by
    simpa only [Controller.Horn.NormalizeLoop.recordOffset, List.take_zero, List.map_nil,
      List.sum_nil, Nat.add_zero] using initial.records.endpoint
  have readyLive : ready.liveWords = state.liveWords + 5 * n + 6 := by
    unfold State.liveWords
    rw [readySize, readyStack, readyOutput, saved]
    simp only [List.length_cons]
    omega
  have headerBelow : layout.recordHeader < state.heap.size := by
    have headerBefore := layout.headersBefore layout.recordHeader (by simp)
    have directoryBefore := layout.directoryBefore
    have sourceBefore := layout.sourceBefore
    unfold Controller.Horn.SourceDirectory.sourceOffset at sourceBefore
    rw [baseEq] at sourceBefore
    omega
  obtain ⟨final, finalMarks, ticks, peak, normalize, complete, finalPC, timeBound,
      spaceBound, frame, finalStack, finalOutput⟩ :=
    normalizer_saved_execution layout.recordHeader program (entry + 42) clauses layout
      normalizerAt (state.heap.size + 5 * n + 4)
      (Controller.Horn.Worklist.IndexedNormalize.Marks.initial n) ready initial dual readyPC
      (by omega) (by rw [readySize]; exact room) (by rw [readySize]; omega)
      (by rw [baseEq]; omega) headersAbove
  refine ⟨final, finalMarks, (25 * n + 58) + ticks,
    max (state.liveWords + 5 * n + 6) peak, prepare.append normalize,
    complete, ?_, by omega, ?_, finalStack.trans readyStack, finalOutput.trans readyOutput, ?_⟩
  · simpa only [Nat.add_assoc] using finalPC
  · rw [readyLive] at spaceBound
    omega
  · exact Controller.Cost.ForestZeroBackendFrame.trans
      ⟨by omega, by rw [readySize]; omega, readyCells⟩ frame

/-- Retained dictionary regions are reinterpreted on the actual backend heap.
Only the physical prefix frame and its allocation-derived region endpoints are
used; the terminal solver does not supply an independent slot table. -/
def retainedDictionaryLayout (before after : Array (Word width)) (prefixSize : Nat)
    (layout : ForestZeroDictionary.Layout ambient before.size)
    (frame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame prefixSize before after)
    (tableBefore : layout.tableBase + ambient ≤ prefixSize)
    (inverseBefore : layout.inverseBase + ambient ≤ prefixSize) :
    ForestZeroDictionary.Layout ambient after.size where
  tableBase := layout.tableBase
  inverseBase := layout.inverseBase
  tableBound := le_trans tableBefore frame.2.1
  inverseBound := le_trans inverseBefore frame.2.1
  disjoint := layout.disjoint

theorem dictionary_prefix_transport (before after : Array (Word width)) (prefixSize : Nat)
    (layout : ForestZeroDictionary.Layout ambient before.size) (dictionary : Dictionary ambient)
    (represented : Represented before layout dictionary)
    (frame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame prefixSize before after)
    (tableBefore : layout.tableBase + ambient ≤ prefixSize)
    (inverseBefore : layout.inverseBase + ambient ≤ prefixSize) :
    Represented after (retainedDictionaryLayout before after prefixSize layout frame tableBefore inverseBefore)
      dictionary := by
  refine ⟨represented.coherent, ?_, ?_⟩
  · intro coordinate
    change after[layout.tableBase + coordinate.val]? = _
    exact (frame.2.2 _ (by have := coordinate.isLt; omega)).trans (represented.slots coordinate)
  · intro index coordinate allocated
    change after[layout.inverseBase + index]? = _
    have indexBound : index < dictionary.coordinates.size :=
      (Array.getElem?_eq_some_iff.mp allocated).1
    have countBound := ForestZeroDictionary.count_le_ambient dictionary represented.coherent
    exact (frame.2.2 _ (by omega)).trans (represented.inverse index coordinate allocated)

/-- The original global count words survive the same protected prefix used for
solver and dictionary framing. They are not supplied as prepared registers. -/
theorem projection_headers_transport (before after : Array (Word width)) (prefixSize channels nodes : Nat)
    (frame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame prefixSize before after)
    (headersBefore : 1 < prefixSize)
    (channelsCell : before[0]? = some (word width channels))
    (nodesCell : before[1]? = some (word width nodes)) :
    after[0]? = some (word width channels) ∧ after[1]? = some (word width nodes) := by
  exact ⟨(frame.2.2 0 (by omega)).trans channelsCell, (frame.2.2 1 headersBefore).trans nodesCell⟩

def channelPrepareCode (width : Nat) : Program width 8 :=
  #[.pop 0, .pop 4, .pop 3, .pop 7, .push 7, .push 3, .push 4, .push 0,
    .constant 6 (word width (2 ^ width - 1)),
    .constant 0 (word width 0), .load 0 0, .copy 3 0,
    .constant 0 (word width 1), .load 0 0, .add 0 0 3,
    .xor 0 0 6, .add 0 0 5, .add 4 4 0, .add 7 7 5]

@[simp] theorem channelPrepareCode_size (width : Nat) :
    (channelPrepareCode width).size = 19 := rfl

private theorem channelPrepare_complement (value : Nat) (fits : value < 2 ^ width) :
    Nat.xor value (2 ^ width - 1) = 2 ^ width - 1 - value := by
  have equal := congrArg BitVec.toNat (BitVec.xor_allOnes (x := BitVec.ofNat width value))
  simpa only [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits,
    BitVec.toNat_allOnes, BitVec.toNat_not, Nat.xor_eq] using equal

private theorem channelPrepare_difference (smaller larger : Nat)
    (fits : larger < 2 ^ width) (ordered : smaller ≤ larger) :
    word width ((word width larger).val +
      (word width ((word width (Nat.xor smaller (2 ^ width - 1))).val + 1)).val) =
      word width (larger - smaller) := by
  have positive := Nat.two_pow_pos width
  have smallerFits : smaller < 2 ^ width := by omega
  have complementFits : 2 ^ width - 1 - smaller < 2 ^ width := by omega
  rw [channelPrepare_complement smaller smallerFits,
    show (word width larger).val = larger from Nat.mod_eq_of_lt fits,
    show (word width (2 ^ width - 1 - smaller)).val = 2 ^ width - 1 - smaller
      from Nat.mod_eq_of_lt complementFits]
  have sumEq : larger + (2 ^ width - 1 - smaller + 1) = larger - smaller + 2 ^ width := by omega
  apply Fin.ext
  simp only [word]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, sumEq, Nat.add_mod_right]


/-- Flat physical register states keep each fetched transition independent
of the other preparation instructions. Registers2/5 retain real zero/one. -/
private def projectionConfiguration (template : State width 8) (cursor : Nat)
    (value0 value3 value4 value6 value7 : Word width) (stack : List (Word width)) : State width 8 :=
  { template with
    pc := word width cursor
    stack := stack
    reg := fun register => if register = 0 then value0 else
      if register = 3 then value3 else if register = 4 then value4 else
      if register = 6 then value6 else if register = 7 then value7 else template.reg register }

private theorem projectionConfiguration_heap (template : State width 8) (cursor : Nat)
    (a b c d e : Word width) (stack : List (Word width)) :
    (projectionConfiguration template cursor a b c d e stack).heap = template.heap := rfl

private theorem projectionConfiguration_live (template : State width 8) (cursor : Nat)
    (a b c d e : Word width) (stack : List (Word width)) :
    (projectionConfiguration template cursor a b c d e stack).liveWords =
      9 + template.heap.size + stack.length + template.output.length := by
  simp only [projectionConfiguration, State.liveWords]
  omega

/-- Source headers and saved allocator base fix the projection addresses.
The local caller derives adjacency from its once-only dictionary allocation. -/
theorem channelPrepare_geometry (table inverse channels nodes base : Nat)
    (dictionaryAdjacent : inverse = table + (channels + nodes)) :
    inverse - (channels + nodes) = table ∧ base + 1 = base + 1 := by
  constructor
  · omega
  · rfl

private theorem projection_state_eq (first second : State width 8)
    (registers : first.reg = second.reg) (heap : first.heap = second.heap)
    (stack : first.stack = second.stack) (output : first.output = second.output)
    (position : first.pc = second.pc) (running : first.halted = second.halted) :
    first = second := by
  cases first
  cases second
  simp_all

/-- The concrete layout supplies every scalar room bound needed by the fixed
subtraction; local-count size is retained only for later touched-slot reset. -/
theorem projection_scalar_bounds (heap : Array (Word width))
    (table inverse channels nodes base : Nat)
    (heapFits : heap.size < 2 ^ width)
    (tableAdjacent : inverse = table + (channels + nodes))
    (dictionaryBound : inverse + (channels + nodes) ≤ base)
    (scratchBound : base + 4 ≤ heap.size) :
    channels < 2 ^ width ∧ nodes < 2 ^ width ∧
      channels + nodes ≤ inverse ∧ inverse < 2 ^ width ∧
      channels + nodes < 2 ^ width ∧ base + 1 < 2 ^ width := by
  omega

private theorem projection_transition_0 (program : Program width 8) (state : State width 8) (entry : Nat)
    (count inverse localCount baseWord : Word width) (rest : List (Word width))
    (table base channels nodes : Nat)
    (inverseEq : inverse = word width (table + (channels + nodes)))
    (baseEq : baseWord = word width base)
    (running : state.halted = false) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? =
      (channelPrepareCode width)[phase.val]?) :
    programStep program (projectionConfiguration state (entry + 0) (state.reg 0) (state.reg 3) (state.reg 4) (state.reg 6) (state.reg 7) (count :: inverse :: localCount :: baseWord :: rest)) = some (projectionConfiguration state (entry + 1) count (state.reg 3) (state.reg 4) (state.reg 6) (state.reg 7) (inverse :: localCount :: baseWord :: rest)) := by
  let before := projectionConfiguration state (entry + 0) (state.reg 0) (state.reg 3) (state.reg 4) (state.reg 6) (state.reg 7) (count :: inverse :: localCount :: baseWord :: rest)
  let after := projectionConfiguration state (entry + 1) count (state.reg 3) (state.reg 4) (state.reg 6) (state.reg 7) (inverse :: localCount :: baseWord :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 19) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have powerPositive := Nat.two_pow_pos width
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have inverseFits : table + (channels + nodes) < 2 ^ width := scalarRoom
  have maskFits : 2 ^ width - 1 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have pcValue : (word width (entry + 0)).val = entry + 0 :=
    Nat.mod_eq_of_lt (pcFits 0 (by decide))
  have nextPC : entry + 0 + 1 = entry + 1 := by omega
  change programStep program before = some after
  rw [fetched8 program before (entry + 0) (.pop 0) rfl (pcFits 0 (by decide))
    (by simpa [channelPrepareCode] using present ⟨0, by decide⟩)]
  simp only [step, before, projectionConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  apply congrArg some
  apply projection_state_eq
  · funext register
    fin_cases register <;> simp only [after, projectionConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem projection_transition_1 (program : Program width 8) (state : State width 8) (entry : Nat)
    (count inverse localCount baseWord : Word width) (rest : List (Word width))
    (table base channels nodes : Nat)
    (inverseEq : inverse = word width (table + (channels + nodes)))
    (baseEq : baseWord = word width base)
    (running : state.halted = false) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? =
      (channelPrepareCode width)[phase.val]?) :
    programStep program (projectionConfiguration state (entry + 1) count (state.reg 3) (state.reg 4) (state.reg 6) (state.reg 7) (inverse :: localCount :: baseWord :: rest)) = some (projectionConfiguration state (entry + 2) count (state.reg 3) inverse (state.reg 6) (state.reg 7) (localCount :: baseWord :: rest)) := by
  let before := projectionConfiguration state (entry + 1) count (state.reg 3) (state.reg 4) (state.reg 6) (state.reg 7) (inverse :: localCount :: baseWord :: rest)
  let after := projectionConfiguration state (entry + 2) count (state.reg 3) inverse (state.reg 6) (state.reg 7) (localCount :: baseWord :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 19) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have powerPositive := Nat.two_pow_pos width
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have inverseFits : table + (channels + nodes) < 2 ^ width := scalarRoom
  have maskFits : 2 ^ width - 1 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have pcValue : (word width (entry + 1)).val = entry + 1 :=
    Nat.mod_eq_of_lt (pcFits 1 (by decide))
  have nextPC : entry + 1 + 1 = entry + 2 := by omega
  change programStep program before = some after
  rw [fetched8 program before (entry + 1) (.pop 4) rfl (pcFits 1 (by decide))
    (by simpa [channelPrepareCode] using present ⟨1, by decide⟩)]
  simp only [step, before, projectionConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  apply congrArg some
  apply projection_state_eq
  · funext register
    fin_cases register <;> simp only [after, projectionConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem projection_transition_2 (program : Program width 8) (state : State width 8) (entry : Nat)
    (count inverse localCount baseWord : Word width) (rest : List (Word width))
    (table base channels nodes : Nat)
    (inverseEq : inverse = word width (table + (channels + nodes)))
    (baseEq : baseWord = word width base)
    (running : state.halted = false) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? =
      (channelPrepareCode width)[phase.val]?) :
    programStep program (projectionConfiguration state (entry + 2) count (state.reg 3) inverse (state.reg 6) (state.reg 7) (localCount :: baseWord :: rest)) = some (projectionConfiguration state (entry + 3) count localCount inverse (state.reg 6) (state.reg 7) (baseWord :: rest)) := by
  let before := projectionConfiguration state (entry + 2) count (state.reg 3) inverse (state.reg 6) (state.reg 7) (localCount :: baseWord :: rest)
  let after := projectionConfiguration state (entry + 3) count localCount inverse (state.reg 6) (state.reg 7) (baseWord :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 19) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have powerPositive := Nat.two_pow_pos width
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have inverseFits : table + (channels + nodes) < 2 ^ width := scalarRoom
  have maskFits : 2 ^ width - 1 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have pcValue : (word width (entry + 2)).val = entry + 2 :=
    Nat.mod_eq_of_lt (pcFits 2 (by decide))
  have nextPC : entry + 2 + 1 = entry + 3 := by omega
  change programStep program before = some after
  rw [fetched8 program before (entry + 2) (.pop 3) rfl (pcFits 2 (by decide))
    (by simpa [channelPrepareCode] using present ⟨2, by decide⟩)]
  simp only [step, before, projectionConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  apply congrArg some
  apply projection_state_eq
  · funext register
    fin_cases register <;> simp only [after, projectionConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem projection_transition_3 (program : Program width 8) (state : State width 8) (entry : Nat)
    (count inverse localCount baseWord : Word width) (rest : List (Word width))
    (table base channels nodes : Nat)
    (inverseEq : inverse = word width (table + (channels + nodes)))
    (baseEq : baseWord = word width base)
    (running : state.halted = false) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? =
      (channelPrepareCode width)[phase.val]?) :
    programStep program (projectionConfiguration state (entry + 3) count localCount inverse (state.reg 6) (state.reg 7) (baseWord :: rest)) = some (projectionConfiguration state (entry + 4) count localCount inverse (state.reg 6) baseWord rest) := by
  let before := projectionConfiguration state (entry + 3) count localCount inverse (state.reg 6) (state.reg 7) (baseWord :: rest)
  let after := projectionConfiguration state (entry + 4) count localCount inverse (state.reg 6) baseWord rest
  have pcFits (offset : Nat) (bound : offset ≤ 19) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have powerPositive := Nat.two_pow_pos width
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have inverseFits : table + (channels + nodes) < 2 ^ width := scalarRoom
  have maskFits : 2 ^ width - 1 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have pcValue : (word width (entry + 3)).val = entry + 3 :=
    Nat.mod_eq_of_lt (pcFits 3 (by decide))
  have nextPC : entry + 3 + 1 = entry + 4 := by omega
  change programStep program before = some after
  rw [fetched8 program before (entry + 3) (.pop 7) rfl (pcFits 3 (by decide))
    (by simpa [channelPrepareCode] using present ⟨3, by decide⟩)]
  simp only [step, before, projectionConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  apply congrArg some
  apply projection_state_eq
  · funext register
    fin_cases register <;> simp only [after, projectionConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem projection_transition_4 (program : Program width 8) (state : State width 8) (entry : Nat)
    (count inverse localCount baseWord : Word width) (rest : List (Word width))
    (table base channels nodes : Nat)
    (inverseEq : inverse = word width (table + (channels + nodes)))
    (baseEq : baseWord = word width base)
    (running : state.halted = false) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? =
      (channelPrepareCode width)[phase.val]?) :
    programStep program (projectionConfiguration state (entry + 4) count localCount inverse (state.reg 6) baseWord rest) = some (projectionConfiguration state (entry + 5) count localCount inverse (state.reg 6) baseWord (baseWord :: rest)) := by
  let before := projectionConfiguration state (entry + 4) count localCount inverse (state.reg 6) baseWord rest
  let after := projectionConfiguration state (entry + 5) count localCount inverse (state.reg 6) baseWord (baseWord :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 19) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have powerPositive := Nat.two_pow_pos width
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have inverseFits : table + (channels + nodes) < 2 ^ width := scalarRoom
  have maskFits : 2 ^ width - 1 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have pcValue : (word width (entry + 4)).val = entry + 4 :=
    Nat.mod_eq_of_lt (pcFits 4 (by decide))
  have nextPC : entry + 4 + 1 = entry + 5 := by omega
  change programStep program before = some after
  rw [fetched8 program before (entry + 4) (.push 7) rfl (pcFits 4 (by decide))
    (by simpa [channelPrepareCode] using present ⟨4, by decide⟩)]
  simp only [step, before, projectionConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  apply congrArg some
  apply projection_state_eq
  · funext register
    fin_cases register <;> simp only [after, projectionConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem projection_transition_5 (program : Program width 8) (state : State width 8) (entry : Nat)
    (count inverse localCount baseWord : Word width) (rest : List (Word width))
    (table base channels nodes : Nat)
    (inverseEq : inverse = word width (table + (channels + nodes)))
    (baseEq : baseWord = word width base)
    (running : state.halted = false) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? =
      (channelPrepareCode width)[phase.val]?) :
    programStep program (projectionConfiguration state (entry + 5) count localCount inverse (state.reg 6) baseWord (baseWord :: rest)) = some (projectionConfiguration state (entry + 6) count localCount inverse (state.reg 6) baseWord (localCount :: baseWord :: rest)) := by
  let before := projectionConfiguration state (entry + 5) count localCount inverse (state.reg 6) baseWord (baseWord :: rest)
  let after := projectionConfiguration state (entry + 6) count localCount inverse (state.reg 6) baseWord (localCount :: baseWord :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 19) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have powerPositive := Nat.two_pow_pos width
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have inverseFits : table + (channels + nodes) < 2 ^ width := scalarRoom
  have maskFits : 2 ^ width - 1 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have pcValue : (word width (entry + 5)).val = entry + 5 :=
    Nat.mod_eq_of_lt (pcFits 5 (by decide))
  have nextPC : entry + 5 + 1 = entry + 6 := by omega
  change programStep program before = some after
  rw [fetched8 program before (entry + 5) (.push 3) rfl (pcFits 5 (by decide))
    (by simpa [channelPrepareCode] using present ⟨5, by decide⟩)]
  simp only [step, before, projectionConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  apply congrArg some
  apply projection_state_eq
  · funext register
    fin_cases register <;> simp only [after, projectionConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem projection_transition_6 (program : Program width 8) (state : State width 8) (entry : Nat)
    (count inverse localCount baseWord : Word width) (rest : List (Word width))
    (table base channels nodes : Nat)
    (inverseEq : inverse = word width (table + (channels + nodes)))
    (baseEq : baseWord = word width base)
    (running : state.halted = false) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? =
      (channelPrepareCode width)[phase.val]?) :
    programStep program (projectionConfiguration state (entry + 6) count localCount inverse (state.reg 6) baseWord (localCount :: baseWord :: rest)) = some (projectionConfiguration state (entry + 7) count localCount inverse (state.reg 6) baseWord (inverse :: localCount :: baseWord :: rest)) := by
  let before := projectionConfiguration state (entry + 6) count localCount inverse (state.reg 6) baseWord (localCount :: baseWord :: rest)
  let after := projectionConfiguration state (entry + 7) count localCount inverse (state.reg 6) baseWord (inverse :: localCount :: baseWord :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 19) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have powerPositive := Nat.two_pow_pos width
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have inverseFits : table + (channels + nodes) < 2 ^ width := scalarRoom
  have maskFits : 2 ^ width - 1 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have pcValue : (word width (entry + 6)).val = entry + 6 :=
    Nat.mod_eq_of_lt (pcFits 6 (by decide))
  have nextPC : entry + 6 + 1 = entry + 7 := by omega
  change programStep program before = some after
  rw [fetched8 program before (entry + 6) (.push 4) rfl (pcFits 6 (by decide))
    (by simpa [channelPrepareCode] using present ⟨6, by decide⟩)]
  simp only [step, before, projectionConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  apply congrArg some
  apply projection_state_eq
  · funext register
    fin_cases register <;> simp only [after, projectionConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem projection_transition_7 (program : Program width 8) (state : State width 8) (entry : Nat)
    (count inverse localCount baseWord : Word width) (rest : List (Word width))
    (table base channels nodes : Nat)
    (inverseEq : inverse = word width (table + (channels + nodes)))
    (baseEq : baseWord = word width base)
    (running : state.halted = false) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? =
      (channelPrepareCode width)[phase.val]?) :
    programStep program (projectionConfiguration state (entry + 7) count localCount inverse (state.reg 6) baseWord (inverse :: localCount :: baseWord :: rest)) = some (projectionConfiguration state (entry + 8) count localCount inverse (state.reg 6) baseWord (count :: inverse :: localCount :: baseWord :: rest)) := by
  let before := projectionConfiguration state (entry + 7) count localCount inverse (state.reg 6) baseWord (inverse :: localCount :: baseWord :: rest)
  let after := projectionConfiguration state (entry + 8) count localCount inverse (state.reg 6) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 19) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have powerPositive := Nat.two_pow_pos width
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have inverseFits : table + (channels + nodes) < 2 ^ width := scalarRoom
  have maskFits : 2 ^ width - 1 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have pcValue : (word width (entry + 7)).val = entry + 7 :=
    Nat.mod_eq_of_lt (pcFits 7 (by decide))
  have nextPC : entry + 7 + 1 = entry + 8 := by omega
  change programStep program before = some after
  rw [fetched8 program before (entry + 7) (.push 0) rfl (pcFits 7 (by decide))
    (by simpa [channelPrepareCode] using present ⟨7, by decide⟩)]
  simp only [step, before, projectionConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  apply congrArg some
  apply projection_state_eq
  · funext register
    fin_cases register <;> simp only [after, projectionConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem projection_transition_8 (program : Program width 8) (state : State width 8) (entry : Nat)
    (count inverse localCount baseWord : Word width) (rest : List (Word width))
    (table base channels nodes : Nat)
    (inverseEq : inverse = word width (table + (channels + nodes)))
    (baseEq : baseWord = word width base)
    (running : state.halted = false) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? =
      (channelPrepareCode width)[phase.val]?) :
    programStep program (projectionConfiguration state (entry + 8) count localCount inverse (state.reg 6) baseWord (count :: inverse :: localCount :: baseWord :: rest)) = some (projectionConfiguration state (entry + 9) count localCount inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)) := by
  let before := projectionConfiguration state (entry + 8) count localCount inverse (state.reg 6) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  let after := projectionConfiguration state (entry + 9) count localCount inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 19) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have powerPositive := Nat.two_pow_pos width
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have inverseFits : table + (channels + nodes) < 2 ^ width := scalarRoom
  have maskFits : 2 ^ width - 1 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have pcValue : (word width (entry + 8)).val = entry + 8 :=
    Nat.mod_eq_of_lt (pcFits 8 (by decide))
  have nextPC : entry + 8 + 1 = entry + 9 := by omega
  change programStep program before = some after
  rw [fetched8 program before (entry + 8) (.constant 6 (word width (2 ^ width - 1))) rfl (pcFits 8 (by decide))
    (by simpa [channelPrepareCode] using present ⟨8, by decide⟩)]
  simp only [step, before, projectionConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  apply congrArg some
  apply projection_state_eq
  · funext register
    fin_cases register <;> simp only [after, projectionConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem projection_transition_9 (program : Program width 8) (state : State width 8) (entry : Nat)
    (count inverse localCount baseWord : Word width) (rest : List (Word width))
    (table base channels nodes : Nat)
    (inverseEq : inverse = word width (table + (channels + nodes)))
    (baseEq : baseWord = word width base)
    (running : state.halted = false) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? =
      (channelPrepareCode width)[phase.val]?) :
    programStep program (projectionConfiguration state (entry + 9) count localCount inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)) = some (projectionConfiguration state (entry + 10) (word width 0) localCount inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)) := by
  let before := projectionConfiguration state (entry + 9) count localCount inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  let after := projectionConfiguration state (entry + 10) (word width 0) localCount inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 19) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have powerPositive := Nat.two_pow_pos width
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have inverseFits : table + (channels + nodes) < 2 ^ width := scalarRoom
  have maskFits : 2 ^ width - 1 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have pcValue : (word width (entry + 9)).val = entry + 9 :=
    Nat.mod_eq_of_lt (pcFits 9 (by decide))
  have nextPC : entry + 9 + 1 = entry + 10 := by omega
  change programStep program before = some after
  rw [fetched8 program before (entry + 9) (.constant 0 (word width 0)) rfl (pcFits 9 (by decide))
    (by simpa [channelPrepareCode] using present ⟨9, by decide⟩)]
  simp only [step, before, projectionConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  apply congrArg some
  apply projection_state_eq
  · funext register
    fin_cases register <;> simp only [after, projectionConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem projection_transition_10 (program : Program width 8) (state : State width 8) (entry : Nat)
    (count inverse localCount baseWord : Word width) (rest : List (Word width))
    (table base channels nodes : Nat)
    (inverseEq : inverse = word width (table + (channels + nodes)))
    (baseEq : baseWord = word width base)
    (running : state.halted = false) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? =
      (channelPrepareCode width)[phase.val]?) :
    programStep program (projectionConfiguration state (entry + 10) (word width 0) localCount inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)) = some (projectionConfiguration state (entry + 11) (word width channels) localCount inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)) := by
  let before := projectionConfiguration state (entry + 10) (word width 0) localCount inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  let after := projectionConfiguration state (entry + 11) (word width channels) localCount inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 19) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have powerPositive := Nat.two_pow_pos width
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have inverseFits : table + (channels + nodes) < 2 ^ width := scalarRoom
  have maskFits : 2 ^ width - 1 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have pcValue : (word width (entry + 10)).val = entry + 10 :=
    Nat.mod_eq_of_lt (pcFits 10 (by decide))
  have nextPC : entry + 10 + 1 = entry + 11 := by omega
  change programStep program before = some after
  rw [fetched8 program before (entry + 10) (.load 0 0) rfl (pcFits 10 (by decide))
    (by simpa [channelPrepareCode] using present ⟨10, by decide⟩)]
  have addressValue : (word width 0).val = 0 := Nat.mod_eq_of_lt (by omega)
  have cell : state.heap[0]'(by omega) = word width channels := by
    have actual := channelCell
    rw [Array.getElem?_eq_getElem (show 0 < state.heap.size by omega)] at actual
    exact Option.some.inj actual
  simp only [step, before, projectionConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true, addressValue, dite_eq_left (show 0 < state.heap.size by omega), cell]
  apply congrArg some
  apply projection_state_eq
  · funext register
    fin_cases register <;> simp only [after, projectionConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem projection_transition_11 (program : Program width 8) (state : State width 8) (entry : Nat)
    (count inverse localCount baseWord : Word width) (rest : List (Word width))
    (table base channels nodes : Nat)
    (inverseEq : inverse = word width (table + (channels + nodes)))
    (baseEq : baseWord = word width base)
    (running : state.halted = false) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? =
      (channelPrepareCode width)[phase.val]?) :
    programStep program (projectionConfiguration state (entry + 11) (word width channels) localCount inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)) = some (projectionConfiguration state (entry + 12) (word width channels) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)) := by
  let before := projectionConfiguration state (entry + 11) (word width channels) localCount inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  let after := projectionConfiguration state (entry + 12) (word width channels) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 19) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have powerPositive := Nat.two_pow_pos width
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have inverseFits : table + (channels + nodes) < 2 ^ width := scalarRoom
  have maskFits : 2 ^ width - 1 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have pcValue : (word width (entry + 11)).val = entry + 11 :=
    Nat.mod_eq_of_lt (pcFits 11 (by decide))
  have nextPC : entry + 11 + 1 = entry + 12 := by omega
  change programStep program before = some after
  rw [fetched8 program before (entry + 11) (.copy 3 0) rfl (pcFits 11 (by decide))
    (by simpa [channelPrepareCode] using present ⟨11, by decide⟩)]
  simp only [step, before, projectionConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  apply congrArg some
  apply projection_state_eq
  · funext register
    fin_cases register <;> simp only [after, projectionConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem projection_transition_12 (program : Program width 8) (state : State width 8) (entry : Nat)
    (count inverse localCount baseWord : Word width) (rest : List (Word width))
    (table base channels nodes : Nat)
    (inverseEq : inverse = word width (table + (channels + nodes)))
    (baseEq : baseWord = word width base)
    (running : state.halted = false) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? =
      (channelPrepareCode width)[phase.val]?) :
    programStep program (projectionConfiguration state (entry + 12) (word width channels) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)) = some (projectionConfiguration state (entry + 13) (word width 1) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)) := by
  let before := projectionConfiguration state (entry + 12) (word width channels) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  let after := projectionConfiguration state (entry + 13) (word width 1) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 19) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have powerPositive := Nat.two_pow_pos width
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have inverseFits : table + (channels + nodes) < 2 ^ width := scalarRoom
  have maskFits : 2 ^ width - 1 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have pcValue : (word width (entry + 12)).val = entry + 12 :=
    Nat.mod_eq_of_lt (pcFits 12 (by decide))
  have nextPC : entry + 12 + 1 = entry + 13 := by omega
  change programStep program before = some after
  rw [fetched8 program before (entry + 12) (.constant 0 (word width 1)) rfl (pcFits 12 (by decide))
    (by simpa [channelPrepareCode] using present ⟨12, by decide⟩)]
  simp only [step, before, projectionConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  apply congrArg some
  apply projection_state_eq
  · funext register
    fin_cases register <;> simp only [after, projectionConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem projection_transition_13 (program : Program width 8) (state : State width 8) (entry : Nat)
    (count inverse localCount baseWord : Word width) (rest : List (Word width))
    (table base channels nodes : Nat)
    (inverseEq : inverse = word width (table + (channels + nodes)))
    (baseEq : baseWord = word width base)
    (running : state.halted = false) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? =
      (channelPrepareCode width)[phase.val]?) :
    programStep program (projectionConfiguration state (entry + 13) (word width 1) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)) = some (projectionConfiguration state (entry + 14) (word width nodes) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)) := by
  let before := projectionConfiguration state (entry + 13) (word width 1) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  let after := projectionConfiguration state (entry + 14) (word width nodes) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 19) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have powerPositive := Nat.two_pow_pos width
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have inverseFits : table + (channels + nodes) < 2 ^ width := scalarRoom
  have maskFits : 2 ^ width - 1 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have pcValue : (word width (entry + 13)).val = entry + 13 :=
    Nat.mod_eq_of_lt (pcFits 13 (by decide))
  have nextPC : entry + 13 + 1 = entry + 14 := by omega
  change programStep program before = some after
  rw [fetched8 program before (entry + 13) (.load 0 0) rfl (pcFits 13 (by decide))
    (by simpa [channelPrepareCode] using present ⟨13, by decide⟩)]
  have addressValue : (word width 1).val = 1 := Nat.mod_eq_of_lt (by omega)
  have cell : state.heap[1]'(by omega) = word width nodes := by
    have actual := nodeCell
    rw [Array.getElem?_eq_getElem (show 1 < state.heap.size by omega)] at actual
    exact Option.some.inj actual
  simp only [step, before, projectionConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true, addressValue, dite_eq_left (show 1 < state.heap.size by omega), cell]
  apply congrArg some
  apply projection_state_eq
  · funext register
    fin_cases register <;> simp only [after, projectionConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem projection_transition_14 (program : Program width 8) (state : State width 8) (entry : Nat)
    (count inverse localCount baseWord : Word width) (rest : List (Word width))
    (table base channels nodes : Nat)
    (inverseEq : inverse = word width (table + (channels + nodes)))
    (baseEq : baseWord = word width base)
    (running : state.halted = false) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? =
      (channelPrepareCode width)[phase.val]?) :
    programStep program (projectionConfiguration state (entry + 14) (word width nodes) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)) = some (projectionConfiguration state (entry + 15) (word width (channels + nodes)) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)) := by
  let before := projectionConfiguration state (entry + 14) (word width nodes) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  let after := projectionConfiguration state (entry + 15) (word width (channels + nodes)) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 19) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have powerPositive := Nat.two_pow_pos width
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have inverseFits : table + (channels + nodes) < 2 ^ width := scalarRoom
  have maskFits : 2 ^ width - 1 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have pcValue : (word width (entry + 14)).val = entry + 14 :=
    Nat.mod_eq_of_lt (pcFits 14 (by decide))
  have nextPC : entry + 14 + 1 = entry + 15 := by omega
  change programStep program before = some after
  rw [fetched8 program before (entry + 14) (.add 0 0 3) rfl (pcFits 14 (by decide))
    (by simpa [channelPrepareCode] using present ⟨14, by decide⟩)]
  simp only [step, before, projectionConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  rw [show (word width nodes).val = nodes from Nat.mod_eq_of_lt nodeFits,
    show (word width channels).val = channels from Nat.mod_eq_of_lt channelFits,
    show nodes + channels = channels + nodes by omega]
  apply congrArg some
  apply projection_state_eq
  · funext register
    fin_cases register <;> simp only [after, projectionConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem projection_transition_15 (program : Program width 8) (state : State width 8) (entry : Nat)
    (count inverse localCount baseWord : Word width) (rest : List (Word width))
    (table base channels nodes : Nat)
    (inverseEq : inverse = word width (table + (channels + nodes)))
    (baseEq : baseWord = word width base)
    (running : state.halted = false) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? =
      (channelPrepareCode width)[phase.val]?) :
    programStep program (projectionConfiguration state (entry + 15) (word width (channels + nodes)) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)) = some (projectionConfiguration state (entry + 16) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)) := by
  let before := projectionConfiguration state (entry + 15) (word width (channels + nodes)) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  let after := projectionConfiguration state (entry + 16) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 19) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have powerPositive := Nat.two_pow_pos width
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have inverseFits : table + (channels + nodes) < 2 ^ width := scalarRoom
  have maskFits : 2 ^ width - 1 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have pcValue : (word width (entry + 15)).val = entry + 15 :=
    Nat.mod_eq_of_lt (pcFits 15 (by decide))
  have nextPC : entry + 15 + 1 = entry + 16 := by omega
  change programStep program before = some after
  rw [fetched8 program before (entry + 15) (.xor 0 0 6) rfl (pcFits 15 (by decide))
    (by simpa [channelPrepareCode] using present ⟨15, by decide⟩)]
  simp only [step, before, projectionConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  rw [show (word width (channels + nodes)).val = channels + nodes from Nat.mod_eq_of_lt ambientFits,
    show (word width (2 ^ width - 1)).val = 2 ^ width - 1 from Nat.mod_eq_of_lt maskFits]
  apply congrArg some
  apply projection_state_eq
  · funext register
    fin_cases register <;> simp only [after, projectionConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem projection_transition_16 (program : Program width 8) (state : State width 8) (entry : Nat)
    (count inverse localCount baseWord : Word width) (rest : List (Word width))
    (table base channels nodes : Nat)
    (inverseEq : inverse = word width (table + (channels + nodes)))
    (baseEq : baseWord = word width base)
    (running : state.halted = false) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? =
      (channelPrepareCode width)[phase.val]?) :
    programStep program (projectionConfiguration state (entry + 16) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)) = some (projectionConfiguration state (entry + 17) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)) := by
  let before := projectionConfiguration state (entry + 16) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  let after := projectionConfiguration state (entry + 17) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 19) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have powerPositive := Nat.two_pow_pos width
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have inverseFits : table + (channels + nodes) < 2 ^ width := scalarRoom
  have maskFits : 2 ^ width - 1 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have pcValue : (word width (entry + 16)).val = entry + 16 :=
    Nat.mod_eq_of_lt (pcFits 16 (by decide))
  have nextPC : entry + 16 + 1 = entry + 17 := by omega
  change programStep program before = some after
  rw [fetched8 program before (entry + 16) (.add 0 0 5) rfl (pcFits 16 (by decide))
    (by simpa [channelPrepareCode] using present ⟨16, by decide⟩)]
  simp only [step, before, projectionConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  rw [one, show (word width 1).val = 1 from Nat.mod_eq_of_lt oneFits]
  apply congrArg some
  apply projection_state_eq
  · funext register
    fin_cases register <;> simp only [after, projectionConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem projection_transition_17 (program : Program width 8) (state : State width 8) (entry : Nat)
    (count inverse localCount baseWord : Word width) (rest : List (Word width))
    (table base channels nodes : Nat)
    (inverseEq : inverse = word width (table + (channels + nodes)))
    (baseEq : baseWord = word width base)
    (running : state.halted = false) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? =
      (channelPrepareCode width)[phase.val]?) :
    programStep program (projectionConfiguration state (entry + 17) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)) = some (projectionConfiguration state (entry + 18) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width channels) (word width table) (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)) := by
  let before := projectionConfiguration state (entry + 17) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width channels) inverse (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  let after := projectionConfiguration state (entry + 18) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width channels) (word width table) (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 19) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have powerPositive := Nat.two_pow_pos width
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have inverseFits : table + (channels + nodes) < 2 ^ width := scalarRoom
  have maskFits : 2 ^ width - 1 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have pcValue : (word width (entry + 17)).val = entry + 17 :=
    Nat.mod_eq_of_lt (pcFits 17 (by decide))
  have nextPC : entry + 17 + 1 = entry + 18 := by omega
  change programStep program before = some after
  rw [fetched8 program before (entry + 17) (.add 4 4 0) rfl (pcFits 17 (by decide))
    (by simpa [channelPrepareCode] using present ⟨17, by decide⟩)]
  simp only [step, before, projectionConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  rw [inverseEq, channelPrepare_difference (channels + nodes) (table + (channels + nodes))
    scalarRoom (by omega), show table + (channels + nodes) - (channels + nodes) = table by omega]
  apply congrArg some
  apply projection_state_eq
  · funext register
    fin_cases register <;> simp only [after, projectionConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem projection_transition_18 (program : Program width 8) (state : State width 8) (entry : Nat)
    (count inverse localCount baseWord : Word width) (rest : List (Word width))
    (table base channels nodes : Nat)
    (inverseEq : inverse = word width (table + (channels + nodes)))
    (baseEq : baseWord = word width base)
    (running : state.halted = false) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? =
      (channelPrepareCode width)[phase.val]?) :
    programStep program (projectionConfiguration state (entry + 18) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width channels) (word width table) (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)) = some (projectionConfiguration state (entry + 19) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width channels) (word width table) (word width (2 ^ width - 1)) (word width (base + 1)) (count :: inverse :: localCount :: baseWord :: rest)) := by
  let before := projectionConfiguration state (entry + 18) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width channels) (word width table) (word width (2 ^ width - 1)) baseWord (count :: inverse :: localCount :: baseWord :: rest)
  let after := projectionConfiguration state (entry + 19) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width channels) (word width table) (word width (2 ^ width - 1)) (word width (base + 1)) (count :: inverse :: localCount :: baseWord :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 19) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have powerPositive := Nat.two_pow_pos width
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have inverseFits : table + (channels + nodes) < 2 ^ width := scalarRoom
  have maskFits : 2 ^ width - 1 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have pcValue : (word width (entry + 18)).val = entry + 18 :=
    Nat.mod_eq_of_lt (pcFits 18 (by decide))
  have nextPC : entry + 18 + 1 = entry + 19 := by omega
  change programStep program before = some after
  rw [fetched8 program before (entry + 18) (.add 7 7 5) rfl (pcFits 18 (by decide))
    (by simpa [channelPrepareCode] using present ⟨18, by decide⟩)]
  simp only [step, before, projectionConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  rw [one, show (word width 1).val = 1 from Nat.mod_eq_of_lt oneFits]
  rw [baseEq, show (word width base).val = base from Nat.mod_eq_of_lt (by omega)]
  apply congrArg some
  apply projection_state_eq
  · funext register
    fin_cases register <;> simp only [after, projectionConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, inverseEq, baseEq]
  · simp only [after, projectionConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem projection_four_trace (program : Program width 8)
    (s0 s1 s2 s3 s4 : State width 8)
    (t0 : programStep program s0 = some s1) (t1 : programStep program s1 = some s2)
    (t2 : programStep program s2 = some s3) (t3 : programStep program s3 = some s4) :
    Execution program s0 s4 4
      (max s0.liveWords (max s1.liveWords (max s2.liveWords (max s3.liveWords s4.liveWords)))) :=
  Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.refl s4))))

private theorem projection_three_trace (program : Program width 8)
    (s0 s1 s2 s3 : State width 8)
    (t0 : programStep program s0 = some s1) (t1 : programStep program s1 = some s2)
    (t2 : programStep program s2 = some s3) :
    Execution program s0 s3 3
      (max s0.liveWords (max s1.liveWords (max s2.liveWords s3.liveWords))) :=
  Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl s3)))

/-- Prepare the original-channel emitter from physically saved allocator words
and the original two loaded headers. No table/off base is loaded from a free
register or recovered from a runtime heap-size oracle. -/
private theorem projection_part_0 (program : Program width 8) (state : State width 8)
    (entry table base channels nodes localCount : Nat) (count : Word width)
    (rest : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (saved : state.stack = count :: word width (table + (channels + nodes)) ::
      word width localCount :: word width base :: rest)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? = (channelPrepareCode width)[phase.val]?) :
    Execution program (projectionConfiguration state (entry + 0) (state.reg 0) (state.reg 3) (state.reg 4) (state.reg 6) (state.reg 7) (count :: (word width (table + (channels + nodes))) :: (word width localCount) :: (word width base) :: rest))
      (projectionConfiguration state (entry + 4) count (word width localCount) (word width (table + (channels + nodes))) (state.reg 6) (word width base) rest) 4 state.liveWords := by
  let inverseWord := word width (table + (channels + nodes))
  let localWord := word width localCount
  let baseWord := word width base
  let s0 := projectionConfiguration state (entry + 0) (state.reg 0) (state.reg 3) (state.reg 4) (state.reg 6) (state.reg 7) (count :: inverseWord :: localWord :: baseWord :: rest)
  let s1 := projectionConfiguration state (entry + 1) count (state.reg 3) (state.reg 4) (state.reg 6) (state.reg 7) (inverseWord :: localWord :: baseWord :: rest)
  let s2 := projectionConfiguration state (entry + 2) count (state.reg 3) inverseWord (state.reg 6) (state.reg 7) (localWord :: baseWord :: rest)
  let s3 := projectionConfiguration state (entry + 3) count localWord inverseWord (state.reg 6) (state.reg 7) (baseWord :: rest)
  let s4 := projectionConfiguration state (entry + 4) count localWord inverseWord (state.reg 6) baseWord rest
  have t0 : programStep program s0 = some s1 :=
    projection_transition_0 program state entry count inverseWord localWord baseWord rest
      table base channels nodes rfl rfl running one headerRoom channelCell nodeCell
      scalarRoom offRoom capacity present
  have t1 : programStep program s1 = some s2 :=
    projection_transition_1 program state entry count inverseWord localWord baseWord rest
      table base channels nodes rfl rfl running one headerRoom channelCell nodeCell
      scalarRoom offRoom capacity present
  have t2 : programStep program s2 = some s3 :=
    projection_transition_2 program state entry count inverseWord localWord baseWord rest
      table base channels nodes rfl rfl running one headerRoom channelCell nodeCell
      scalarRoom offRoom capacity present
  have t3 : programStep program s3 = some s4 :=
    projection_transition_3 program state entry count inverseWord localWord baseWord rest
      table base channels nodes rfl rfl running one headerRoom channelCell nodeCell
      scalarRoom offRoom capacity present
  have initialLive : state.liveWords = 9 + state.heap.size + (4 + rest.length) + state.output.length := by
    simp only [State.liveWords, saved, List.length_cons]
    omega
  have live0 : s0.liveWords + 0 = state.liveWords := by
    simp only [s0, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  have live1 : s1.liveWords + 1 = state.liveWords := by
    simp only [s1, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  have live2 : s2.liveWords + 2 = state.liveWords := by
    simp only [s2, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  have live3 : s3.liveWords + 3 = state.liveWords := by
    simp only [s3, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  have live4 : s4.liveWords + 4 = state.liveWords := by
    simp only [s4, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  convert projection_four_trace program s0 s1 s2 s3 s4 t0 t1 t2 t3 using 1
  all_goals omega

private theorem projection_part_1 (program : Program width 8) (state : State width 8)
    (entry table base channels nodes localCount : Nat) (count : Word width)
    (rest : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (saved : state.stack = count :: word width (table + (channels + nodes)) ::
      word width localCount :: word width base :: rest)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? = (channelPrepareCode width)[phase.val]?) :
    Execution program (projectionConfiguration state (entry + 4) count (word width localCount) (word width (table + (channels + nodes))) (state.reg 6) (word width base) rest)
      (projectionConfiguration state (entry + 8) count (word width localCount) (word width (table + (channels + nodes))) (state.reg 6) (word width base) (count :: (word width (table + (channels + nodes))) :: (word width localCount) :: (word width base) :: rest)) 4 state.liveWords := by
  let inverseWord := word width (table + (channels + nodes))
  let localWord := word width localCount
  let baseWord := word width base
  let s4 := projectionConfiguration state (entry + 4) count localWord inverseWord (state.reg 6) baseWord rest
  let s5 := projectionConfiguration state (entry + 5) count localWord inverseWord (state.reg 6) baseWord (baseWord :: rest)
  let s6 := projectionConfiguration state (entry + 6) count localWord inverseWord (state.reg 6) baseWord (localWord :: baseWord :: rest)
  let s7 := projectionConfiguration state (entry + 7) count localWord inverseWord (state.reg 6) baseWord (inverseWord :: localWord :: baseWord :: rest)
  let s8 := projectionConfiguration state (entry + 8) count localWord inverseWord (state.reg 6) baseWord (count :: inverseWord :: localWord :: baseWord :: rest)
  have t4 : programStep program s4 = some s5 :=
    projection_transition_4 program state entry count inverseWord localWord baseWord rest
      table base channels nodes rfl rfl running one headerRoom channelCell nodeCell
      scalarRoom offRoom capacity present
  have t5 : programStep program s5 = some s6 :=
    projection_transition_5 program state entry count inverseWord localWord baseWord rest
      table base channels nodes rfl rfl running one headerRoom channelCell nodeCell
      scalarRoom offRoom capacity present
  have t6 : programStep program s6 = some s7 :=
    projection_transition_6 program state entry count inverseWord localWord baseWord rest
      table base channels nodes rfl rfl running one headerRoom channelCell nodeCell
      scalarRoom offRoom capacity present
  have t7 : programStep program s7 = some s8 :=
    projection_transition_7 program state entry count inverseWord localWord baseWord rest
      table base channels nodes rfl rfl running one headerRoom channelCell nodeCell
      scalarRoom offRoom capacity present
  have initialLive : state.liveWords = 9 + state.heap.size + (4 + rest.length) + state.output.length := by
    simp only [State.liveWords, saved, List.length_cons]
    omega
  have live4 : s4.liveWords + 4 = state.liveWords := by
    simp only [s4, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  have live5 : s5.liveWords + 3 = state.liveWords := by
    simp only [s5, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  have live6 : s6.liveWords + 2 = state.liveWords := by
    simp only [s6, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  have live7 : s7.liveWords + 1 = state.liveWords := by
    simp only [s7, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  have live8 : s8.liveWords + 0 = state.liveWords := by
    simp only [s8, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  convert projection_four_trace program s4 s5 s6 s7 s8 t4 t5 t6 t7 using 1
  all_goals omega

private theorem projection_part_2 (program : Program width 8) (state : State width 8)
    (entry table base channels nodes localCount : Nat) (count : Word width)
    (rest : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (saved : state.stack = count :: word width (table + (channels + nodes)) ::
      word width localCount :: word width base :: rest)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? = (channelPrepareCode width)[phase.val]?) :
    Execution program (projectionConfiguration state (entry + 8) count (word width localCount) (word width (table + (channels + nodes))) (state.reg 6) (word width base) (count :: (word width (table + (channels + nodes))) :: (word width localCount) :: (word width base) :: rest))
      (projectionConfiguration state (entry + 12) (word width channels) (word width channels) (word width (table + (channels + nodes))) (word width (2 ^ width - 1)) (word width base) (count :: (word width (table + (channels + nodes))) :: (word width localCount) :: (word width base) :: rest)) 4 state.liveWords := by
  let inverseWord := word width (table + (channels + nodes))
  let localWord := word width localCount
  let baseWord := word width base
  let s8 := projectionConfiguration state (entry + 8) count localWord inverseWord (state.reg 6) baseWord (count :: inverseWord :: localWord :: baseWord :: rest)
  let s9 := projectionConfiguration state (entry + 9) count localWord inverseWord (word width (2 ^ width - 1)) baseWord (count :: inverseWord :: localWord :: baseWord :: rest)
  let s10 := projectionConfiguration state (entry + 10) (word width 0) localWord inverseWord (word width (2 ^ width - 1)) baseWord (count :: inverseWord :: localWord :: baseWord :: rest)
  let s11 := projectionConfiguration state (entry + 11) (word width channels) localWord inverseWord (word width (2 ^ width - 1)) baseWord (count :: inverseWord :: localWord :: baseWord :: rest)
  let s12 := projectionConfiguration state (entry + 12) (word width channels) (word width channels) inverseWord (word width (2 ^ width - 1)) baseWord (count :: inverseWord :: localWord :: baseWord :: rest)
  have t8 : programStep program s8 = some s9 :=
    projection_transition_8 program state entry count inverseWord localWord baseWord rest
      table base channels nodes rfl rfl running one headerRoom channelCell nodeCell
      scalarRoom offRoom capacity present
  have t9 : programStep program s9 = some s10 :=
    projection_transition_9 program state entry count inverseWord localWord baseWord rest
      table base channels nodes rfl rfl running one headerRoom channelCell nodeCell
      scalarRoom offRoom capacity present
  have t10 : programStep program s10 = some s11 :=
    projection_transition_10 program state entry count inverseWord localWord baseWord rest
      table base channels nodes rfl rfl running one headerRoom channelCell nodeCell
      scalarRoom offRoom capacity present
  have t11 : programStep program s11 = some s12 :=
    projection_transition_11 program state entry count inverseWord localWord baseWord rest
      table base channels nodes rfl rfl running one headerRoom channelCell nodeCell
      scalarRoom offRoom capacity present
  have initialLive : state.liveWords = 9 + state.heap.size + (4 + rest.length) + state.output.length := by
    simp only [State.liveWords, saved, List.length_cons]
    omega
  have live8 : s8.liveWords + 0 = state.liveWords := by
    simp only [s8, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  have live9 : s9.liveWords + 0 = state.liveWords := by
    simp only [s9, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  have live10 : s10.liveWords + 0 = state.liveWords := by
    simp only [s10, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  have live11 : s11.liveWords + 0 = state.liveWords := by
    simp only [s11, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  have live12 : s12.liveWords + 0 = state.liveWords := by
    simp only [s12, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  convert projection_four_trace program s8 s9 s10 s11 s12 t8 t9 t10 t11 using 1
  all_goals omega

private theorem projection_part_3 (program : Program width 8) (state : State width 8)
    (entry table base channels nodes localCount : Nat) (count : Word width)
    (rest : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (saved : state.stack = count :: word width (table + (channels + nodes)) ::
      word width localCount :: word width base :: rest)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? = (channelPrepareCode width)[phase.val]?) :
    Execution program (projectionConfiguration state (entry + 12) (word width channels) (word width channels) (word width (table + (channels + nodes))) (word width (2 ^ width - 1)) (word width base) (count :: (word width (table + (channels + nodes))) :: (word width localCount) :: (word width base) :: rest))
      (projectionConfiguration state (entry + 16) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) (word width (table + (channels + nodes))) (word width (2 ^ width - 1)) (word width base) (count :: (word width (table + (channels + nodes))) :: (word width localCount) :: (word width base) :: rest)) 4 state.liveWords := by
  let inverseWord := word width (table + (channels + nodes))
  let localWord := word width localCount
  let baseWord := word width base
  let s12 := projectionConfiguration state (entry + 12) (word width channels) (word width channels) inverseWord (word width (2 ^ width - 1)) baseWord (count :: inverseWord :: localWord :: baseWord :: rest)
  let s13 := projectionConfiguration state (entry + 13) (word width 1) (word width channels) inverseWord (word width (2 ^ width - 1)) baseWord (count :: inverseWord :: localWord :: baseWord :: rest)
  let s14 := projectionConfiguration state (entry + 14) (word width nodes) (word width channels) inverseWord (word width (2 ^ width - 1)) baseWord (count :: inverseWord :: localWord :: baseWord :: rest)
  let s15 := projectionConfiguration state (entry + 15) (word width (channels + nodes)) (word width channels) inverseWord (word width (2 ^ width - 1)) baseWord (count :: inverseWord :: localWord :: baseWord :: rest)
  let s16 := projectionConfiguration state (entry + 16) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) inverseWord (word width (2 ^ width - 1)) baseWord (count :: inverseWord :: localWord :: baseWord :: rest)
  have t12 : programStep program s12 = some s13 :=
    projection_transition_12 program state entry count inverseWord localWord baseWord rest
      table base channels nodes rfl rfl running one headerRoom channelCell nodeCell
      scalarRoom offRoom capacity present
  have t13 : programStep program s13 = some s14 :=
    projection_transition_13 program state entry count inverseWord localWord baseWord rest
      table base channels nodes rfl rfl running one headerRoom channelCell nodeCell
      scalarRoom offRoom capacity present
  have t14 : programStep program s14 = some s15 :=
    projection_transition_14 program state entry count inverseWord localWord baseWord rest
      table base channels nodes rfl rfl running one headerRoom channelCell nodeCell
      scalarRoom offRoom capacity present
  have t15 : programStep program s15 = some s16 :=
    projection_transition_15 program state entry count inverseWord localWord baseWord rest
      table base channels nodes rfl rfl running one headerRoom channelCell nodeCell
      scalarRoom offRoom capacity present
  have initialLive : state.liveWords = 9 + state.heap.size + (4 + rest.length) + state.output.length := by
    simp only [State.liveWords, saved, List.length_cons]
    omega
  have live12 : s12.liveWords + 0 = state.liveWords := by
    simp only [s12, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  have live13 : s13.liveWords + 0 = state.liveWords := by
    simp only [s13, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  have live14 : s14.liveWords + 0 = state.liveWords := by
    simp only [s14, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  have live15 : s15.liveWords + 0 = state.liveWords := by
    simp only [s15, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  have live16 : s16.liveWords + 0 = state.liveWords := by
    simp only [s16, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  convert projection_four_trace program s12 s13 s14 s15 s16 t12 t13 t14 t15 using 1
  all_goals omega

private theorem projection_part_4 (program : Program width 8) (state : State width 8)
    (entry table base channels nodes localCount : Nat) (count : Word width)
    (rest : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (saved : state.stack = count :: word width (table + (channels + nodes)) ::
      word width localCount :: word width base :: rest)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? = (channelPrepareCode width)[phase.val]?) :
    Execution program (projectionConfiguration state (entry + 16) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) (word width (table + (channels + nodes))) (word width (2 ^ width - 1)) (word width base) (count :: (word width (table + (channels + nodes))) :: (word width localCount) :: (word width base) :: rest))
      (projectionConfiguration state (entry + 19) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width channels) (word width table) (word width (2 ^ width - 1)) (word width (base + 1)) (count :: (word width (table + (channels + nodes))) :: (word width localCount) :: (word width base) :: rest)) 3 state.liveWords := by
  let inverseWord := word width (table + (channels + nodes))
  let localWord := word width localCount
  let baseWord := word width base
  let s16 := projectionConfiguration state (entry + 16) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) inverseWord (word width (2 ^ width - 1)) baseWord (count :: inverseWord :: localWord :: baseWord :: rest)
  let s17 := projectionConfiguration state (entry + 17) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width channels) inverseWord (word width (2 ^ width - 1)) baseWord (count :: inverseWord :: localWord :: baseWord :: rest)
  let s18 := projectionConfiguration state (entry + 18) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width channels) (word width table) (word width (2 ^ width - 1)) baseWord (count :: inverseWord :: localWord :: baseWord :: rest)
  let s19 := projectionConfiguration state (entry + 19) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width channels) (word width table) (word width (2 ^ width - 1)) (word width (base + 1)) (count :: inverseWord :: localWord :: baseWord :: rest)
  have t16 : programStep program s16 = some s17 :=
    projection_transition_16 program state entry count inverseWord localWord baseWord rest
      table base channels nodes rfl rfl running one headerRoom channelCell nodeCell
      scalarRoom offRoom capacity present
  have t17 : programStep program s17 = some s18 :=
    projection_transition_17 program state entry count inverseWord localWord baseWord rest
      table base channels nodes rfl rfl running one headerRoom channelCell nodeCell
      scalarRoom offRoom capacity present
  have t18 : programStep program s18 = some s19 :=
    projection_transition_18 program state entry count inverseWord localWord baseWord rest
      table base channels nodes rfl rfl running one headerRoom channelCell nodeCell
      scalarRoom offRoom capacity present
  have initialLive : state.liveWords = 9 + state.heap.size + (4 + rest.length) + state.output.length := by
    simp only [State.liveWords, saved, List.length_cons]
    omega
  have live16 : s16.liveWords + 0 = state.liveWords := by
    simp only [s16, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  have live17 : s17.liveWords + 0 = state.liveWords := by
    simp only [s17, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  have live18 : s18.liveWords + 0 = state.liveWords := by
    simp only [s18, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  have live19 : s19.liveWords + 0 = state.liveWords := by
    simp only [s19, projectionConfiguration_live, List.length_cons]
    rw [initialLive]
    omega
  convert projection_three_trace program s16 s17 s18 s19 t16 t17 t18 using 1
  all_goals omega

theorem channel_prepare_execution (program : Program width 8) (state : State width 8)
    (entry table base channels nodes localCount : Nat) (count : Word width)
    (rest : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (saved : state.stack = count :: word width (table + (channels + nodes)) ::
      word width localCount :: word width base :: rest)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width) (capacity : entry + 19 < 2 ^ width)
    (present : ∀ phase : Fin 19, program[entry + phase.val]? = (channelPrepareCode width)[phase.val]?) :
    ∃ final, Execution program state final 19 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 2 = word width 0 ∧ final.reg 3 = word width channels ∧
      final.reg 4 = word width table ∧ final.reg 5 = word width 1 ∧
      final.reg 6 = word width (2 ^ width - 1) ∧ final.reg 7 = word width (base + 1) ∧
      final.pc = word width (entry + 19) ∧ final.halted = false := by
  let inverseWord := word width (table + (channels + nodes))
  let localWord := word width localCount
  let baseWord := word width base
  let s0 := projectionConfiguration state (entry + 0) (state.reg 0) (state.reg 3) (state.reg 4) (state.reg 6) (state.reg 7) (count :: inverseWord :: localWord :: baseWord :: rest)
  let s4 := projectionConfiguration state (entry + 4) count localWord inverseWord (state.reg 6) baseWord rest
  let s8 := projectionConfiguration state (entry + 8) count localWord inverseWord (state.reg 6) baseWord (count :: inverseWord :: localWord :: baseWord :: rest)
  let s12 := projectionConfiguration state (entry + 12) (word width channels) (word width channels) inverseWord (word width (2 ^ width - 1)) baseWord (count :: inverseWord :: localWord :: baseWord :: rest)
  let s16 := projectionConfiguration state (entry + 16) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) inverseWord (word width (2 ^ width - 1)) baseWord (count :: inverseWord :: localWord :: baseWord :: rest)
  let s19 := projectionConfiguration state (entry + 19) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width channels) (word width table) (word width (2 ^ width - 1)) (word width (base + 1)) (count :: inverseWord :: localWord :: baseWord :: rest)
  have initialEq : s0 = state := by
    apply projection_state_eq
    · funext register
      fin_cases register <;> simp [s0, projectionConfiguration]
    · rfl
    · exact saved.symm
    · rfl
    · simpa only [s0, projectionConfiguration, Nat.add_zero] using position.symm
    · rfl
  have part0 : Execution program s0 s4 4 state.liveWords :=
    projection_part_0 program state entry table base channels nodes localCount count rest position running saved zero one headerRoom channelCell nodeCell scalarRoom offRoom capacity present
  have part1 : Execution program s4 s8 4 state.liveWords :=
    projection_part_1 program state entry table base channels nodes localCount count rest position running saved zero one headerRoom channelCell nodeCell scalarRoom offRoom capacity present
  have part2 : Execution program s8 s12 4 state.liveWords :=
    projection_part_2 program state entry table base channels nodes localCount count rest position running saved zero one headerRoom channelCell nodeCell scalarRoom offRoom capacity present
  have part3 : Execution program s12 s16 4 state.liveWords :=
    projection_part_3 program state entry table base channels nodes localCount count rest position running saved zero one headerRoom channelCell nodeCell scalarRoom offRoom capacity present
  have part4 : Execution program s16 s19 3 state.liveWords :=
    projection_part_4 program state entry table base channels nodes localCount count rest position running saved zero one headerRoom channelCell nodeCell scalarRoom offRoom capacity present
  have whole : Execution program state s19 19 state.liveWords := by
    rw [initialEq] at part0
    simpa only [Nat.max_self] using (((part0.append part1).append part2).append part3).append part4
  refine ⟨s19, whole, rfl, saved.symm, rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, running⟩
  · simpa [s19, projectionConfiguration] using zero
  · simp [s19, projectionConfiguration]
  · simp [s19, projectionConfiguration]
  · simpa [s19, projectionConfiguration] using one
  · simp [s19, projectionConfiguration]
  · simp [s19, projectionConfiguration]

/-- Real saved allocator words and retained global headers form all emitter
registers before the original-channel output and physical suffix release.
The dictionary and terminal FIFO determine the emitted bits. -/
theorem prepared_dictionary_emission_reclaim {channels ambient : Nat}
    (program : Program width 8) (state : State width 8)
    (entry cleanupEntry returnPc base keep count nodes : Nat)
    (dictionary : Dictionary ambient)
    (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : Represented state.heap layout dictionary)
    (ambientEq : ambient = channels + nodes)
    (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (queue : List (Fin dictionary.coordinates.size))
    (fifo : Controller.Horn.WorklistMark.Stored queue base state.heap)
    (localFit : dictionary.coordinates.size + 1 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (headerRoom : 1 < state.heap.size)
    (channelsFit : channels + 1 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width)
    (prepareCapacity : entry + 33 < 2 ^ width)
    (prepareAt : ∀ phase : Fin 19, program[entry + phase.val]? = (channelPrepareCode width)[phase.val]?)
    (emitAt : Controller.Cost.ForestZeroChannelEmit.CodeAt program (entry + 19) cleanupEntry)
    (setupAt : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (loopAt : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width) (countFits : count < 2 ^ width)
    (rest : List (Word width))
    (saved : state.stack = word width count :: word width layout.inverseBase ::
      word width dictionary.coordinates.size :: word width base :: rest)
    (allocated : state.heap.size = keep + count)
    (tableBefore : layout.tableBase + ambient ≤ keep)
    (inverseBefore : layout.inverseBase + ambient ≤ keep) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 13 * channels + 4 * count + 24 ∧ peak ≤ state.liveWords + channels ∧
      final.heap.size = keep ∧
      final.stack = word width layout.inverseBase :: word width dictionary.coordinates.size ::
        word width base :: rest ∧
      final.output = (List.finRange channels).map (fun channel =>
        Controller.Cost.ForestZeroChannelEmit.bitWord width
          (ForestZeroModelLift.lift dictionary true
            (Controller.Cost.ForestZeroChannelEmit.localValues queue)
            ⟨channel.val, by rw [ambientEq]; have := channel.isLt; omega⟩)) ++ state.output ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame keep state.heap final.heap := by
  have scalarRoom : layout.tableBase + (channels + nodes) < 2 ^ width := by
    have inverseBound := layout.inverseBound
    have inverseScalar : layout.inverseBase = layout.tableBase + (channels + nodes) :=
      adjacent.trans (congrArg (fun value => layout.tableBase + value) ambientEq)
    omega
  have prepareSaved : state.stack = word width count ::
      word width (layout.tableBase + (channels + nodes)) ::
      word width dictionary.coordinates.size :: word width base :: rest := by
    simpa only [adjacent, ambientEq] using saved
  obtain ⟨prepared, preparation, sameHeap, sameStack, sameOutput,
      preparedZero, preparedChannels, preparedTable, preparedOne, preparedMask, preparedOff,
      preparedPC, preparedRunning⟩ :=
    channel_prepare_execution program state entry layout.tableBase base channels nodes
      dictionary.coordinates.size (word width count) rest position running prepareSaved zero one
      headerRoom channelCell nodeCell scalarRoom offRoom (by omega) prepareAt
  have unchanged : Controller.Cost.ForestZeroBackendFrame.PrefixFrame keep state.heap prepared.heap :=
    ⟨by omega, by rw [sameHeap]; omega, fun _ _ => by rw [sameHeap]⟩
  let preparedLayout := retainedDictionaryLayout state.heap prepared.heap keep layout unchanged
    tableBefore inverseBefore
  have preparedDictionary : Represented prepared.heap preparedLayout dictionary :=
    dictionary_prefix_transport state.heap prepared.heap keep layout dictionary represented
      unchanged tableBefore inverseBefore
  have preparedFifo : Controller.Horn.WorklistMark.Stored queue base prepared.heap := by
    simpa only [sameHeap] using fifo
  have within : channels ≤ ambient := by rw [ambientEq]; omega
  obtain ⟨final, ticks, peak, emitted, timeBound, spaceBound, finalSize, finalStack,
      finalOutput, finalPC, finalRunning, frame⟩ :=
    Controller.Cost.ForestZeroAnswerReclaim.dictionary_emission_reclaim program prepared
      (entry + 19) cleanupEntry returnPc base keep count dictionary preparedLayout
      preparedDictionary within queue preparedFifo localFit preparedPC preparedRunning
      preparedZero preparedChannels preparedTable preparedOne preparedMask preparedOff
      channelsFit (by rw [sameHeap]; omega) (by omega) emitAt setupAt loopAt cleanupCapacity
      countFits (word width layout.inverseBase :: word width dictionary.coordinates.size ::
        word width base :: rest) (sameStack.trans saved)
      (by rw [sameHeap]; exact allocated)
  have preparedLive : prepared.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [sameHeap, sameStack, sameOutput]
  refine ⟨final, 19 + ticks, max state.liveWords peak, preparation.append emitted,
    by omega, ?_, finalSize, finalStack, ?_, finalPC, finalRunning, ?_⟩
  · rw [preparedLive] at spaceBound
    omega
  · simpa only [sameOutput] using finalOutput
  · exact Controller.Cost.ForestZeroBackendFrame.trans unchanged frame

/-- Two fetched constants establish the projection registers after the backend. -/
def projectionConstantsCode (width : Nat) : Array (Instruction width 8) :=
  #[.constant 2 (word width 0), .constant 5 (word width 1)]

/-- Establish zero and one by actual instructions, retaining every physical
allocation word, the terminal model heap, and the emitted answer. -/
theorem projection_constants_execution (program : Program width 8)
    (state : State width 8) (entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 2 < 2 ^ width)
    (present : ∀ phase : Fin 2, program[entry + phase.val]? =
      (projectionConstantsCode width)[phase.val]?) :
    ∃ final, Execution program state final 2 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 2 = word width 0 ∧ final.reg 5 = word width 1 ∧
      final.pc = word width (entry + 2) ∧ final.halted = false := by
  let first : State width 8 := state.advance.put 2 (word width 0)
  let final : State width 8 := first.advance.put 5 (word width 1)
  have entryValue : (word width entry).val = entry := Nat.mod_eq_of_lt (by omega)
  have nextValue : (word width (entry + 1)).val = entry + 1 :=
    Nat.mod_eq_of_lt (by omega)
  have firstPC : first.pc = word width (entry + 1) := by
    simp only [first, State.put, State.advance, position, entryValue]
  have firstRunning : first.halted = false := running
  have firstStep : programStep program state = some first := by
    rw [fetched8 program state entry (.constant 2 (word width 0)) position
      (by omega) (by simpa [projectionConstantsCode] using present 0)]
    simp only [step, running, Bool.false_eq_true, ↓reduceIte]
    rfl
  have finalStep : programStep program first = some final := by
    rw [fetched8 program first (entry + 1) (.constant 5 (word width 1)) firstPC
      (by omega) (by simpa [projectionConstantsCode] using present 1)]
    simp only [step, firstRunning, Bool.false_eq_true, ↓reduceIte]
    rfl
  have firstLive : first.liveWords = state.liveWords := rfl
  have finalLive : final.liveWords = state.liveWords := rfl
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · convert Execution.cons firstStep (Execution.cons finalStep (Execution.refl final)) using 1 <;>
      simp only [firstLive, finalLive, Nat.max_self] <;> omega
  · simp [final, first, State.put, State.advance]
  · simp [final, State.put]
  · simp only [final, State.put, State.advance, firstPC, nextValue]
  · exact firstRunning


theorem terminal_dictionary_emission_reclaim {channels ambient : Nat}
    (program : Program width 8) (state : State width 8)
    (entry cleanupEntry returnPc base keep count nodes : Nat)
    (dictionary : Dictionary ambient)
    (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : Represented state.heap layout dictionary)
    (ambientEq : ambient = channels + nodes)
    (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (queue : List (Fin dictionary.coordinates.size))
    (fifo : Controller.Horn.WorklistMark.Stored queue base state.heap)
    (localFit : dictionary.coordinates.size + 1 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (headerRoom : 1 < state.heap.size)
    (channelsFit : channels + 1 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (offRoom : base + 1 < 2 ^ width)
    (prepareCapacity : entry + 35 < 2 ^ width)
    (constantsAt : ∀ phase : Fin 2, program[entry + phase.val]? = (projectionConstantsCode width)[phase.val]?)
    (prepareAt : ∀ phase : Fin 19, program[entry + 2 + phase.val]? = (channelPrepareCode width)[phase.val]?)
    (emitAt : Controller.Cost.ForestZeroChannelEmit.CodeAt program (entry + 21) cleanupEntry)
    (setupAt : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (loopAt : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width) (countFits : count < 2 ^ width)
    (rest : List (Word width))
    (saved : state.stack = word width count :: word width layout.inverseBase ::
      word width dictionary.coordinates.size :: word width base :: rest)
    (allocated : state.heap.size = keep + count)
    (tableBefore : layout.tableBase + ambient ≤ keep)
    (inverseBefore : layout.inverseBase + ambient ≤ keep) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 13 * channels + 4 * count + 26 ∧ peak ≤ state.liveWords + channels ∧
      final.heap.size = keep ∧
      final.stack = word width layout.inverseBase :: word width dictionary.coordinates.size ::
        word width base :: rest ∧
      final.output = (List.finRange channels).map (fun channel =>
        Controller.Cost.ForestZeroChannelEmit.bitWord width
          (ForestZeroModelLift.lift dictionary true
            (Controller.Cost.ForestZeroChannelEmit.localValues queue)
            ⟨channel.val, by rw [ambientEq]; have := channel.isLt; omega⟩)) ++ state.output ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame keep state.heap final.heap := by
  obtain ⟨ready, constants, readyHeap, readyStack, readyOutput, readyZero, readyOne,
      readyPC, readyRunning⟩ := projection_constants_execution program state entry
    position running (by omega) constantsAt
  have readyFrame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame keep state.heap ready.heap :=
    ⟨by omega, by rw [readyHeap]; omega, fun _ _ => by rw [readyHeap]⟩
  let readyLayout := retainedDictionaryLayout state.heap ready.heap keep layout readyFrame
    tableBefore inverseBefore
  have readyDictionary : Represented ready.heap readyLayout dictionary :=
    dictionary_prefix_transport state.heap ready.heap keep layout dictionary represented
      readyFrame tableBefore inverseBefore
  have readyFifo : Controller.Horn.WorklistMark.Stored queue base ready.heap := by
    simpa only [readyHeap] using fifo
  obtain ⟨final, ticks, peak, trace, timeBound, spaceBound, finalSize, finalStack,
      finalOutput, finalPC, finalRunning, frame⟩ :=
    prepared_dictionary_emission_reclaim program ready (entry + 2) cleanupEntry returnPc
      base keep count nodes dictionary readyLayout readyDictionary ambientEq adjacent queue readyFifo
      localFit readyPC readyRunning readyZero readyOne
      (by simpa only [readyHeap] using channelCell)
      (by simpa only [readyHeap] using nodeCell)
      (by simpa only [readyHeap] using headerRoom) channelsFit
      (by simpa only [readyHeap] using heapFits) offRoom
      (by omega) prepareAt (by simpa only [Nat.add_assoc] using emitAt)
      setupAt loopAt cleanupCapacity countFits rest (readyStack.trans saved)
      (by rw [readyHeap]; exact allocated) tableBefore inverseBefore
  have readyLive : ready.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [readyHeap, readyStack, readyOutput]
  refine ⟨final, 2 + ticks, max state.liveWords peak, constants.append trace,
    by omega, ?_, finalSize, finalStack, ?_, finalPC, finalRunning, ?_⟩
  · rw [readyLive] at spaceBound
    omega
  · simpa only [readyOutput] using finalOutput
  · exact Controller.Cost.ForestZeroBackendFrame.trans readyFrame frame


theorem initialized_original_projection_execution {channels ambient : Nat}
    (dictionary : Dictionary ambient) (keep : Nat)
    (formula : Controller.CNF.Formula (Fin dictionary.coordinates.size)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex (formula.clauses.toList) recordStart recordEnd base
      (Controller.Horn.IndexScan.occurrences (formula.clauses.toList) recordStart).length state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Controller.Horn.WorklistMark.Stored ([] : List (Fin dictionary.coordinates.size)) base state.heap)
    (separated : base + 5 * dictionary.coordinates.size + 4 ≤ recordStart)
    (setupAt : ∀ phase : Fin 10, program[entry + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := dictionary.coordinates.size) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := dictionary.coordinates.size) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size < 2 ^ width) (setupCapacity : entry + 10 < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : keep ≤ state.heap.size) (prefixBelow : keep ≤ base)
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := dictionary.coordinates.size) width base fetch)[phase.val]?)
    (headCapacity : seedDone + 4 < 2 ^ width)
    (fifoDone bucket advance ready skip : Nat)
    (fetchAt : Controller.Horn.WorklistFIFO.FetchAt (n := dictionary.coordinates.size) program base fetch fifoDone bucket)
    (advanceAt : Controller.Horn.WorklistFIFO.AdvanceAt (n := dictionary.coordinates.size) program base advance fetch)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program bucket advance ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := dictionary.coordinates.size) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (projectionEntry cleanupEntry returnPc : Nat)
    (successAt : Controller.Cost.ForestZeroAnswer.At program fifoDone 1 projectionEntry)
    (conflictAt : Controller.Cost.ForestZeroAnswer.At program conflict 0 cleanupEntry)
    (successCapacity : fifoDone + 4 < 2 ^ width)
    (conflictCapacity : conflict + 4 < 2 ^ width)
    (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : Represented state.heap layout dictionary)
    (nodes count : Nat)
    (ambientEq : ambient = channels + nodes)
    (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (tableBefore : layout.tableBase + ambient ≤ keep)
    (inverseBefore : layout.inverseBase + ambient ≤ keep)
    (headersBefore : 1 < keep)
    (channelsCell : state.heap[0]? = some (word width channels))
    (nodesCell : state.heap[1]? = some (word width nodes))
    (localFit : dictionary.coordinates.size + 1 < 2 ^ width)
    (channelsFit : channels + 1 < 2 ^ width) (offRoom : base + 1 < 2 ^ width)
    (projectionCapacity : projectionEntry + 35 < 2 ^ width)
    (constantsAt : ∀ phase : Fin 2, program[projectionEntry + phase.val]? =
      (projectionConstantsCode width)[phase.val]?)
    (preparationAt : ∀ phase : Fin 19, program[projectionEntry + 2 + phase.val]? =
      (channelPrepareCode width)[phase.val]?)
    (emitAt : Controller.Cost.ForestZeroChannelEmit.CodeAt program (projectionEntry + 21) cleanupEntry)
    (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (cleanupLoop : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width) (countFits : count < 2 ^ width)
    (rest : List (Word width))
    (savedCount : state.stack = word width count :: word width layout.inverseBase ::
      word width dictionary.coordinates.size :: word width base :: rest)
    (allocated : state.heap.size = keep + count) :
    ∃ answer : Bool, ∃ queue final ticks peak,
      Execution program state final ticks peak ∧
      ticks ≤ 36 * formula.clauses.toList.length +
        32 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length +
        26 * dictionary.coordinates.size + 13 * channels + 4 * count + 54 ∧
      peak ≤ state.liveWords + channels + 1 ∧ final.heap.size = keep ∧
      final.stack = word width layout.inverseBase :: word width dictionary.coordinates.size ::
        word width base :: rest ∧
      final.output = (if answer then (List.finRange channels).map (fun channel =>
        Controller.Cost.ForestZeroChannelEmit.bitWord width
          (ForestZeroModelLift.lift dictionary true
            (Controller.Cost.ForestZeroChannelEmit.localValues queue)
            ⟨channel.val, by rw [ambientEq]; have := channel.isLt; omega⟩)) ++
          word width 1 :: state.output else word width 0 :: state.output) ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame keep state.heap final.heap ∧
      (answer = true ↔ ∃ assignment, Controller.CNF.Satisfies assignment formula) ∧
      (answer = true → Controller.CNF.Satisfies (Controller.Horn.WorklistOutcome.offAssignment queue) formula ∧
        Controller.Horn.WorklistOutcome.offAssignment queue = Controller.Horn.greatestCandidate formula)
 := by
  obtain ⟨queue, middle, firstTicks, firstBound, first, middleSize,
      middleStack, middleOutput, firstFrame, outcome⟩ :=
    Controller.Cost.ForestZeroOutcome.initialized_original_execution keep formula dual
      recordHeader recordStart recordEnd base entry scan seedDone conflict state program
      physical header fifo separated setupAt scanAt position running zero one room
      setupCapacity scanCapacity prefixBound prefixBelow fetch headAt headCapacity
      fifoDone bucket advance ready skip fetchAt advanceAt loopAt readyAt
      fetchCapacity advanceCapacity bucketCapacity readyCapacity
  have middleLive : middle.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [middleSize, middleStack, middleOutput]
  rcases outcome with ⟨pc, live, noModels⟩ | ⟨fired, finished, model, forced⟩
  · obtain ⟨tagged, tagTrace, tagHeap, tagStack, tagOutput, tagPC, tagRunning, tagFrame⟩ :=
      Controller.Cost.ForestZeroAnswer.execution keep program conflict 0 cleanupEntry middle
        conflictAt pc live conflictCapacity (by omega) (by rw [middleSize]; exact prefixBound)
    let savedRest := word width layout.inverseBase :: word width dictionary.coordinates.size ::
      word width base :: rest
    obtain ⟨final, cleanup, finalSize, finalStack, finalOutput, finalPC, finalRunning, lastFrame⟩ :=
      Controller.Cost.ForestZeroReclaim.stacked_execution program cleanupEntry returnPc keep count
        tagged savedRest cleanupSetup cleanupLoop tagPC tagRunning cleanupCapacity countFits
        (tagStack.trans (middleStack.trans savedCount))
        (by rw [tagHeap, middleSize]; exact allocated)
    have taggedLive : tagged.liveWords = state.liveWords + 1 := by
      unfold State.liveWords
      rw [tagHeap, middleSize, tagStack, middleStack, tagOutput, middleOutput]
      simp only [List.length_cons]
      omega
    refine ⟨false, queue, final, firstTicks + 4 + (4 * count + 4),
      max state.liveWords (max (middle.liveWords + 1) tagged.liveWords),
      (by simpa only [Nat.add_assoc] using first.append (tagTrace.append cleanup)),
      by omega, ?_, finalSize, finalStack,
      ?_, finalPC, finalRunning,
      Controller.Cost.ForestZeroBackendFrame.trans firstFrame
        (Controller.Cost.ForestZeroBackendFrame.trans tagFrame lastFrame), ?_, ?_⟩
    · rw [middleLive, taggedLive]
      omega
    · simpa only [Bool.false_eq_true, ite_false, savedRest, tagOutput, middleOutput] using finalOutput
    · constructor
      · intro impossible
        cases impossible
      · intro possible
        exact False.elim (noModels possible)
    · intro impossible
      cases impossible
  · obtain ⟨tagged, tagTrace, tagHeap, tagStack, tagOutput, tagPC, tagRunning, tagFrame⟩ :=
      Controller.Cost.ForestZeroAnswer.execution keep program fifoDone 1 projectionEntry middle
        successAt finished.position finished.running successCapacity (by omega)
        (by rw [middleSize]; exact prefixBound)
    have taggedFrame := Controller.Cost.ForestZeroBackendFrame.trans firstFrame tagFrame
    let taggedLayout := retainedDictionaryLayout state.heap tagged.heap keep layout taggedFrame
      tableBefore inverseBefore
    have taggedDictionary : Represented tagged.heap taggedLayout dictionary :=
      dictionary_prefix_transport state.heap tagged.heap keep layout dictionary represented
        taggedFrame tableBefore inverseBefore
    have taggedFifo : Controller.Horn.WorklistMark.Stored queue base tagged.heap := by
      simpa only [tagHeap] using finished.fifo
    obtain ⟨channelsStored, nodesStored⟩ := projection_headers_transport state.heap tagged.heap
      keep channels nodes taggedFrame headersBefore channelsCell nodesCell
    obtain ⟨final, lastTicks, lastPeak, suffix, suffixTime, suffixSpace, finalSize, finalStack,
        finalOutput, finalPC, finalRunning, suffixFrame⟩ :=
      terminal_dictionary_emission_reclaim program tagged projectionEntry cleanupEntry returnPc
        base keep count nodes dictionary taggedLayout taggedDictionary ambientEq adjacent queue taggedFifo
        localFit tagPC tagRunning channelsStored nodesStored
        (by have := taggedFrame.2.1; omega) channelsFit (by rw [tagHeap, middleSize]; exact room)
        offRoom projectionCapacity constantsAt preparationAt emitAt cleanupSetup cleanupLoop
        cleanupCapacity countFits rest (tagStack.trans (middleStack.trans savedCount))
        (by rw [tagHeap, middleSize]; exact allocated) tableBefore inverseBefore
    have taggedLive : tagged.liveWords = state.liveWords + 1 := by
      unfold State.liveWords
      rw [tagHeap, middleSize, tagStack, middleStack, tagOutput, middleOutput]
      simp only [List.length_cons]
      omega
    refine ⟨true, queue, final, firstTicks + 4 + lastTicks,
      max state.liveWords (max (middle.liveWords + 1) lastPeak),
      (by simpa only [Nat.add_assoc] using first.append (tagTrace.append suffix)),
      by omega, ?_, finalSize, finalStack,
      ?_, finalPC, finalRunning,
      Controller.Cost.ForestZeroBackendFrame.trans taggedFrame suffixFrame,
      ⟨fun _ => ⟨Controller.Horn.WorklistOutcome.offAssignment queue, model⟩, fun _ => rfl⟩,
      fun _ => ⟨model, Controller.Cost.ForestZeroAnswerReclaim.terminal_greatest formula dual
        queue model forced⟩⟩
    · rw [taggedLive] at suffixSpace
      rw [middleLive]
      omega
    · simpa only [ite_true, tagOutput, middleOutput] using finalOutput


/-- The reset prelude recovers the touched count and inverse from the real
caller stack and computes the table from original stored source headers. -/
def resetPrepareCode (width : Nat) : Program width 4 :=
  #[.pop 2, .pop 0, .pop 3, .constant 1 (word width 0), .load 1 1, .push 0, .constant 0 (word width 1), .load 0 0, .add 0 0 1, .constant 3 (word width (2 ^ width - 1)), .xor 0 0 3, .constant 3 (word width 1), .add 0 0 3, .add 1 2 0, .pop 0]

private def resetPrepareConfiguration (state : State width 4) (entry : Nat)
    (a b c d : Word width) (stack : List (Word width)) : State width 4 :=
  { state with
    pc := word width entry
    stack := stack
    reg := (fun index => if index = 0 then a else if index = 1 then b else if index = 2 then c else d) }

private theorem resetPrepare_state_eq (first second : State width 4)
    (registers : first.reg = second.reg) (heap : first.heap = second.heap)
    (stack : first.stack = second.stack) (output : first.output = second.output)
    (position : first.pc = second.pc) (running : first.halted = second.halted) :
    first = second := by
  cases first
  cases second
  simp_all

private theorem reset_prepare_transition_0 (program : Program width 4) (state : State width 4)
    (entry table channels nodes count : Nat) (savedBase : Word width) (rest : List (Word width))
    (running : state.halted = false)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? =
      (resetPrepareCode width)[phase.val]?) :
    programStep program (resetPrepareConfiguration state (entry + 0) (state.reg 0) (state.reg 1) (state.reg 2) (state.reg 3) (word width (table + (channels + nodes)) :: word width count :: savedBase :: rest)) = some (resetPrepareConfiguration state (entry + 1) (state.reg 0) (state.reg 1) (word width (table + (channels + nodes))) (state.reg 3) (word width count :: savedBase :: rest)) := by
  let before := resetPrepareConfiguration state (entry + 0) (state.reg 0) (state.reg 1) (state.reg 2) (state.reg 3) (word width (table + (channels + nodes)) :: word width count :: savedBase :: rest)
  let after := resetPrepareConfiguration state (entry + 1) (state.reg 0) (state.reg 1) (word width (table + (channels + nodes))) (state.reg 3) (word width count :: savedBase :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have pcValue : (word width (entry + 0)).val = entry + 0 :=
    Nat.mod_eq_of_lt (pcFits 0 (by decide))
  have nextPC : entry + 0 + 1 = entry + 1 := by omega
  change programStep program before = some after
  rw [fetched program before (entry + 0) (.pop 2) rfl (pcFits 0 (by decide))
    (by simpa [resetPrepareCode] using present ⟨0, by decide⟩)]
  simp only [step, before, resetPrepareConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  apply congrArg some
  apply resetPrepare_state_eq
  · funext register
    fin_cases register <;> simp only [after, resetPrepareConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · rfl
  · rfl
  · rfl
  · simp only [after, resetPrepareConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem reset_prepare_transition_1 (program : Program width 4) (state : State width 4)
    (entry table channels nodes count : Nat) (savedBase : Word width) (rest : List (Word width))
    (running : state.halted = false)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? =
      (resetPrepareCode width)[phase.val]?) :
    programStep program (resetPrepareConfiguration state (entry + 1) (state.reg 0) (state.reg 1) (word width (table + (channels + nodes))) (state.reg 3) (word width count :: savedBase :: rest)) = some (resetPrepareConfiguration state (entry + 2) (word width count) (state.reg 1) (word width (table + (channels + nodes))) (state.reg 3) (savedBase :: rest)) := by
  let before := resetPrepareConfiguration state (entry + 1) (state.reg 0) (state.reg 1) (word width (table + (channels + nodes))) (state.reg 3) (word width count :: savedBase :: rest)
  let after := resetPrepareConfiguration state (entry + 2) (word width count) (state.reg 1) (word width (table + (channels + nodes))) (state.reg 3) (savedBase :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have pcValue : (word width (entry + 1)).val = entry + 1 :=
    Nat.mod_eq_of_lt (pcFits 1 (by decide))
  have nextPC : entry + 1 + 1 = entry + 2 := by omega
  change programStep program before = some after
  rw [fetched program before (entry + 1) (.pop 0) rfl (pcFits 1 (by decide))
    (by simpa [resetPrepareCode] using present ⟨1, by decide⟩)]
  simp only [step, before, resetPrepareConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  apply congrArg some
  apply resetPrepare_state_eq
  · funext register
    fin_cases register <;> simp only [after, resetPrepareConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · rfl
  · rfl
  · rfl
  · simp only [after, resetPrepareConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem reset_prepare_transition_2 (program : Program width 4) (state : State width 4)
    (entry table channels nodes count : Nat) (savedBase : Word width) (rest : List (Word width))
    (running : state.halted = false)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? =
      (resetPrepareCode width)[phase.val]?) :
    programStep program (resetPrepareConfiguration state (entry + 2) (word width count) (state.reg 1) (word width (table + (channels + nodes))) (state.reg 3) (savedBase :: rest)) = some (resetPrepareConfiguration state (entry + 3) (word width count) (state.reg 1) (word width (table + (channels + nodes))) savedBase rest) := by
  let before := resetPrepareConfiguration state (entry + 2) (word width count) (state.reg 1) (word width (table + (channels + nodes))) (state.reg 3) (savedBase :: rest)
  let after := resetPrepareConfiguration state (entry + 3) (word width count) (state.reg 1) (word width (table + (channels + nodes))) savedBase rest
  have pcFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have pcValue : (word width (entry + 2)).val = entry + 2 :=
    Nat.mod_eq_of_lt (pcFits 2 (by decide))
  have nextPC : entry + 2 + 1 = entry + 3 := by omega
  change programStep program before = some after
  rw [fetched program before (entry + 2) (.pop 3) rfl (pcFits 2 (by decide))
    (by simpa [resetPrepareCode] using present ⟨2, by decide⟩)]
  simp only [step, before, resetPrepareConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  apply congrArg some
  apply resetPrepare_state_eq
  · funext register
    fin_cases register <;> simp only [after, resetPrepareConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · rfl
  · rfl
  · rfl
  · simp only [after, resetPrepareConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem reset_prepare_transition_3 (program : Program width 4) (state : State width 4)
    (entry table channels nodes count : Nat) (savedBase : Word width) (rest : List (Word width))
    (running : state.halted = false)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? =
      (resetPrepareCode width)[phase.val]?) :
    programStep program (resetPrepareConfiguration state (entry + 3) (word width count) (state.reg 1) (word width (table + (channels + nodes))) savedBase rest) = some (resetPrepareConfiguration state (entry + 4) (word width count) (word width 0) (word width (table + (channels + nodes))) savedBase rest) := by
  let before := resetPrepareConfiguration state (entry + 3) (word width count) (state.reg 1) (word width (table + (channels + nodes))) savedBase rest
  let after := resetPrepareConfiguration state (entry + 4) (word width count) (word width 0) (word width (table + (channels + nodes))) savedBase rest
  have pcFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have pcValue : (word width (entry + 3)).val = entry + 3 :=
    Nat.mod_eq_of_lt (pcFits 3 (by decide))
  have nextPC : entry + 3 + 1 = entry + 4 := by omega
  change programStep program before = some after
  rw [fetched program before (entry + 3) (.constant 1 (word width 0)) rfl (pcFits 3 (by decide))
    (by simpa [resetPrepareCode] using present ⟨3, by decide⟩)]
  simp only [step, before, resetPrepareConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  apply congrArg some
  apply resetPrepare_state_eq
  · funext register
    fin_cases register <;> simp only [after, resetPrepareConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · rfl
  · rfl
  · rfl
  · simp only [after, resetPrepareConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem reset_prepare_transition_4 (program : Program width 4) (state : State width 4)
    (entry table channels nodes count : Nat) (savedBase : Word width) (rest : List (Word width))
    (running : state.halted = false)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? =
      (resetPrepareCode width)[phase.val]?) :
    programStep program (resetPrepareConfiguration state (entry + 4) (word width count) (word width 0) (word width (table + (channels + nodes))) savedBase rest) = some (resetPrepareConfiguration state (entry + 5) (word width count) (word width channels) (word width (table + (channels + nodes))) savedBase rest) := by
  let before := resetPrepareConfiguration state (entry + 4) (word width count) (word width 0) (word width (table + (channels + nodes))) savedBase rest
  let after := resetPrepareConfiguration state (entry + 5) (word width count) (word width channels) (word width (table + (channels + nodes))) savedBase rest
  have pcFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have pcValue : (word width (entry + 4)).val = entry + 4 :=
    Nat.mod_eq_of_lt (pcFits 4 (by decide))
  have nextPC : entry + 4 + 1 = entry + 5 := by omega
  change programStep program before = some after
  rw [fetched program before (entry + 4) (.load 1 1) rfl (pcFits 4 (by decide))
    (by simpa [resetPrepareCode] using present ⟨4, by decide⟩)]
  simp only [step, before, resetPrepareConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  have addressValue : (word width 0).val = 0 := Nat.mod_eq_of_lt (by omega)
  have storedValue : state.heap[0]'(by omega) = word width channels := by
    have cell := channelCell
    rw [Array.getElem?_eq_getElem (show 0 < state.heap.size by omega)] at cell
    exact Option.some.inj cell
  simp only [addressValue, dite_eq_left (show 0 < state.heap.size by omega), storedValue]
  apply congrArg some
  apply resetPrepare_state_eq
  · funext register
    fin_cases register <;> simp only [after, resetPrepareConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · rfl
  · rfl
  · rfl
  · simp only [after, resetPrepareConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem reset_prepare_transition_5 (program : Program width 4) (state : State width 4)
    (entry table channels nodes count : Nat) (savedBase : Word width) (rest : List (Word width))
    (running : state.halted = false)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? =
      (resetPrepareCode width)[phase.val]?) :
    programStep program (resetPrepareConfiguration state (entry + 5) (word width count) (word width channels) (word width (table + (channels + nodes))) savedBase rest) = some (resetPrepareConfiguration state (entry + 6) (word width count) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)) := by
  let before := resetPrepareConfiguration state (entry + 5) (word width count) (word width channels) (word width (table + (channels + nodes))) savedBase rest
  let after := resetPrepareConfiguration state (entry + 6) (word width count) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have pcValue : (word width (entry + 5)).val = entry + 5 :=
    Nat.mod_eq_of_lt (pcFits 5 (by decide))
  have nextPC : entry + 5 + 1 = entry + 6 := by omega
  change programStep program before = some after
  rw [fetched program before (entry + 5) (.push 0) rfl (pcFits 5 (by decide))
    (by simpa [resetPrepareCode] using present ⟨5, by decide⟩)]
  simp only [step, before, resetPrepareConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  apply congrArg some
  apply resetPrepare_state_eq
  · funext register
    fin_cases register <;> simp only [after, resetPrepareConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · rfl
  · rfl
  · rfl
  · simp only [after, resetPrepareConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem reset_prepare_transition_6 (program : Program width 4) (state : State width 4)
    (entry table channels nodes count : Nat) (savedBase : Word width) (rest : List (Word width))
    (running : state.halted = false)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? =
      (resetPrepareCode width)[phase.val]?) :
    programStep program (resetPrepareConfiguration state (entry + 6) (word width count) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)) = some (resetPrepareConfiguration state (entry + 7) (word width 1) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)) := by
  let before := resetPrepareConfiguration state (entry + 6) (word width count) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)
  let after := resetPrepareConfiguration state (entry + 7) (word width 1) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have pcValue : (word width (entry + 6)).val = entry + 6 :=
    Nat.mod_eq_of_lt (pcFits 6 (by decide))
  have nextPC : entry + 6 + 1 = entry + 7 := by omega
  change programStep program before = some after
  rw [fetched program before (entry + 6) (.constant 0 (word width 1)) rfl (pcFits 6 (by decide))
    (by simpa [resetPrepareCode] using present ⟨6, by decide⟩)]
  simp only [step, before, resetPrepareConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  apply congrArg some
  apply resetPrepare_state_eq
  · funext register
    fin_cases register <;> simp only [after, resetPrepareConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · rfl
  · rfl
  · rfl
  · simp only [after, resetPrepareConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem reset_prepare_transition_7 (program : Program width 4) (state : State width 4)
    (entry table channels nodes count : Nat) (savedBase : Word width) (rest : List (Word width))
    (running : state.halted = false)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? =
      (resetPrepareCode width)[phase.val]?) :
    programStep program (resetPrepareConfiguration state (entry + 7) (word width 1) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)) = some (resetPrepareConfiguration state (entry + 8) (word width nodes) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)) := by
  let before := resetPrepareConfiguration state (entry + 7) (word width 1) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)
  let after := resetPrepareConfiguration state (entry + 8) (word width nodes) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have pcValue : (word width (entry + 7)).val = entry + 7 :=
    Nat.mod_eq_of_lt (pcFits 7 (by decide))
  have nextPC : entry + 7 + 1 = entry + 8 := by omega
  change programStep program before = some after
  rw [fetched program before (entry + 7) (.load 0 0) rfl (pcFits 7 (by decide))
    (by simpa [resetPrepareCode] using present ⟨7, by decide⟩)]
  simp only [step, before, resetPrepareConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  have addressValue : (word width 1).val = 1 := Nat.mod_eq_of_lt (by omega)
  have storedValue : state.heap[1]'(by omega) = word width nodes := by
    have cell := nodeCell
    rw [Array.getElem?_eq_getElem (show 1 < state.heap.size by omega)] at cell
    exact Option.some.inj cell
  simp only [addressValue, dite_eq_left headerRoom, storedValue]
  apply congrArg some
  apply resetPrepare_state_eq
  · funext register
    fin_cases register <;> simp only [after, resetPrepareConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · rfl
  · rfl
  · rfl
  · simp only [after, resetPrepareConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem reset_prepare_transition_8 (program : Program width 4) (state : State width 4)
    (entry table channels nodes count : Nat) (savedBase : Word width) (rest : List (Word width))
    (running : state.halted = false)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? =
      (resetPrepareCode width)[phase.val]?) :
    programStep program (resetPrepareConfiguration state (entry + 8) (word width nodes) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)) = some (resetPrepareConfiguration state (entry + 9) (word width (channels + nodes)) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)) := by
  let before := resetPrepareConfiguration state (entry + 8) (word width nodes) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)
  let after := resetPrepareConfiguration state (entry + 9) (word width (channels + nodes)) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have pcValue : (word width (entry + 8)).val = entry + 8 :=
    Nat.mod_eq_of_lt (pcFits 8 (by decide))
  have nextPC : entry + 8 + 1 = entry + 9 := by omega
  change programStep program before = some after
  rw [fetched program before (entry + 8) (.add 0 0 1) rfl (pcFits 8 (by decide))
    (by simpa [resetPrepareCode] using present ⟨8, by decide⟩)]
  simp only [step, before, resetPrepareConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  rw [show (word width nodes).val = nodes from Nat.mod_eq_of_lt nodeFits, show (word width channels).val = channels from Nat.mod_eq_of_lt channelFits]
  rw [Nat.add_comm nodes channels]
  apply congrArg some
  apply resetPrepare_state_eq
  · funext register
    fin_cases register <;> simp only [after, resetPrepareConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · rfl
  · rfl
  · rfl
  · simp only [after, resetPrepareConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem reset_prepare_transition_9 (program : Program width 4) (state : State width 4)
    (entry table channels nodes count : Nat) (savedBase : Word width) (rest : List (Word width))
    (running : state.halted = false)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? =
      (resetPrepareCode width)[phase.val]?) :
    programStep program (resetPrepareConfiguration state (entry + 9) (word width (channels + nodes)) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)) = some (resetPrepareConfiguration state (entry + 10) (word width (channels + nodes)) (word width channels) (word width (table + (channels + nodes))) (word width (2 ^ width - 1)) (word width count :: rest)) := by
  let before := resetPrepareConfiguration state (entry + 9) (word width (channels + nodes)) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)
  let after := resetPrepareConfiguration state (entry + 10) (word width (channels + nodes)) (word width channels) (word width (table + (channels + nodes))) (word width (2 ^ width - 1)) (word width count :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have pcValue : (word width (entry + 9)).val = entry + 9 :=
    Nat.mod_eq_of_lt (pcFits 9 (by decide))
  have nextPC : entry + 9 + 1 = entry + 10 := by omega
  change programStep program before = some after
  rw [fetched program before (entry + 9) (.constant 3 (word width (2 ^ width - 1))) rfl (pcFits 9 (by decide))
    (by simpa [resetPrepareCode] using present ⟨9, by decide⟩)]
  simp only [step, before, resetPrepareConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  apply congrArg some
  apply resetPrepare_state_eq
  · funext register
    fin_cases register <;> simp only [after, resetPrepareConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · rfl
  · rfl
  · rfl
  · simp only [after, resetPrepareConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem reset_prepare_transition_10 (program : Program width 4) (state : State width 4)
    (entry table channels nodes count : Nat) (savedBase : Word width) (rest : List (Word width))
    (running : state.halted = false)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? =
      (resetPrepareCode width)[phase.val]?) :
    programStep program (resetPrepareConfiguration state (entry + 10) (word width (channels + nodes)) (word width channels) (word width (table + (channels + nodes))) (word width (2 ^ width - 1)) (word width count :: rest)) = some (resetPrepareConfiguration state (entry + 11) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) (word width (table + (channels + nodes))) (word width (2 ^ width - 1)) (word width count :: rest)) := by
  let before := resetPrepareConfiguration state (entry + 10) (word width (channels + nodes)) (word width channels) (word width (table + (channels + nodes))) (word width (2 ^ width - 1)) (word width count :: rest)
  let after := resetPrepareConfiguration state (entry + 11) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) (word width (table + (channels + nodes))) (word width (2 ^ width - 1)) (word width count :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have pcValue : (word width (entry + 10)).val = entry + 10 :=
    Nat.mod_eq_of_lt (pcFits 10 (by decide))
  have nextPC : entry + 10 + 1 = entry + 11 := by omega
  change programStep program before = some after
  rw [fetched program before (entry + 10) (.xor 0 0 3) rfl (pcFits 10 (by decide))
    (by simpa [resetPrepareCode] using present ⟨10, by decide⟩)]
  simp only [step, before, resetPrepareConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  rw [show (word width (channels + nodes)).val = channels + nodes from Nat.mod_eq_of_lt ambientFits, show (word width (2 ^ width - 1)).val = 2 ^ width - 1 from Nat.mod_eq_of_lt maskFits]
  apply congrArg some
  apply resetPrepare_state_eq
  · funext register
    fin_cases register <;> simp only [after, resetPrepareConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · rfl
  · rfl
  · rfl
  · simp only [after, resetPrepareConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem reset_prepare_transition_11 (program : Program width 4) (state : State width 4)
    (entry table channels nodes count : Nat) (savedBase : Word width) (rest : List (Word width))
    (running : state.halted = false)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? =
      (resetPrepareCode width)[phase.val]?) :
    programStep program (resetPrepareConfiguration state (entry + 11) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) (word width (table + (channels + nodes))) (word width (2 ^ width - 1)) (word width count :: rest)) = some (resetPrepareConfiguration state (entry + 12) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) (word width (table + (channels + nodes))) (word width 1) (word width count :: rest)) := by
  let before := resetPrepareConfiguration state (entry + 11) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) (word width (table + (channels + nodes))) (word width (2 ^ width - 1)) (word width count :: rest)
  let after := resetPrepareConfiguration state (entry + 12) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) (word width (table + (channels + nodes))) (word width 1) (word width count :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have pcValue : (word width (entry + 11)).val = entry + 11 :=
    Nat.mod_eq_of_lt (pcFits 11 (by decide))
  have nextPC : entry + 11 + 1 = entry + 12 := by omega
  change programStep program before = some after
  rw [fetched program before (entry + 11) (.constant 3 (word width 1)) rfl (pcFits 11 (by decide))
    (by simpa [resetPrepareCode] using present ⟨11, by decide⟩)]
  simp only [step, before, resetPrepareConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  apply congrArg some
  apply resetPrepare_state_eq
  · funext register
    fin_cases register <;> simp only [after, resetPrepareConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · rfl
  · rfl
  · rfl
  · simp only [after, resetPrepareConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem reset_prepare_transition_12 (program : Program width 4) (state : State width 4)
    (entry table channels nodes count : Nat) (savedBase : Word width) (rest : List (Word width))
    (running : state.halted = false)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? =
      (resetPrepareCode width)[phase.val]?) :
    programStep program (resetPrepareConfiguration state (entry + 12) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) (word width (table + (channels + nodes))) (word width 1) (word width count :: rest)) = some (resetPrepareConfiguration state (entry + 13) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width channels) (word width (table + (channels + nodes))) (word width 1) (word width count :: rest)) := by
  let before := resetPrepareConfiguration state (entry + 12) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) (word width (table + (channels + nodes))) (word width 1) (word width count :: rest)
  let after := resetPrepareConfiguration state (entry + 13) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width channels) (word width (table + (channels + nodes))) (word width 1) (word width count :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have pcValue : (word width (entry + 12)).val = entry + 12 :=
    Nat.mod_eq_of_lt (pcFits 12 (by decide))
  have nextPC : entry + 12 + 1 = entry + 13 := by omega
  change programStep program before = some after
  rw [fetched program before (entry + 12) (.add 0 0 3) rfl (pcFits 12 (by decide))
    (by simpa [resetPrepareCode] using present ⟨12, by decide⟩)]
  simp only [step, before, resetPrepareConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  rw [show (word width 1).val = 1 from Nat.mod_eq_of_lt oneFits]
  apply congrArg some
  apply resetPrepare_state_eq
  · funext register
    fin_cases register <;> simp only [after, resetPrepareConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · rfl
  · rfl
  · rfl
  · simp only [after, resetPrepareConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem reset_prepare_transition_13 (program : Program width 4) (state : State width 4)
    (entry table channels nodes count : Nat) (savedBase : Word width) (rest : List (Word width))
    (running : state.halted = false)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? =
      (resetPrepareCode width)[phase.val]?) :
    programStep program (resetPrepareConfiguration state (entry + 13) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width channels) (word width (table + (channels + nodes))) (word width 1) (word width count :: rest)) = some (resetPrepareConfiguration state (entry + 14) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width table) (word width (table + (channels + nodes))) (word width 1) (word width count :: rest)) := by
  let before := resetPrepareConfiguration state (entry + 13) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width channels) (word width (table + (channels + nodes))) (word width 1) (word width count :: rest)
  let after := resetPrepareConfiguration state (entry + 14) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width table) (word width (table + (channels + nodes))) (word width 1) (word width count :: rest)
  have pcFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have pcValue : (word width (entry + 13)).val = entry + 13 :=
    Nat.mod_eq_of_lt (pcFits 13 (by decide))
  have nextPC : entry + 13 + 1 = entry + 14 := by omega
  change programStep program before = some after
  rw [fetched program before (entry + 13) (.add 1 2 0) rfl (pcFits 13 (by decide))
    (by simpa [resetPrepareCode] using present ⟨13, by decide⟩)]
  simp only [step, before, resetPrepareConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  rw [channelPrepare_difference (channels + nodes) (table + (channels + nodes)) scalarRoom (by omega), show table + (channels + nodes) - (channels + nodes) = table by omega]
  apply congrArg some
  apply resetPrepare_state_eq
  · funext register
    fin_cases register <;> simp only [after, resetPrepareConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · rfl
  · rfl
  · rfl
  · simp only [after, resetPrepareConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem reset_prepare_transition_14 (program : Program width 4) (state : State width 4)
    (entry table channels nodes count : Nat) (savedBase : Word width) (rest : List (Word width))
    (running : state.halted = false)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? =
      (resetPrepareCode width)[phase.val]?) :
    programStep program (resetPrepareConfiguration state (entry + 14) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width table) (word width (table + (channels + nodes))) (word width 1) (word width count :: rest)) = some (resetPrepareConfiguration state (entry + 15) (word width count) (word width table) (word width (table + (channels + nodes))) (word width 1) rest) := by
  let before := resetPrepareConfiguration state (entry + 14) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width table) (word width (table + (channels + nodes))) (word width 1) (word width count :: rest)
  let after := resetPrepareConfiguration state (entry + 15) (word width count) (word width table) (word width (table + (channels + nodes))) (word width 1) rest
  have pcFits (offset : Nat) (bound : offset ≤ 15) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) capacity
  have ambientFits : channels + nodes < 2 ^ width := by omega
  have channelFits : channels < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have pcValue : (word width (entry + 14)).val = entry + 14 :=
    Nat.mod_eq_of_lt (pcFits 14 (by decide))
  have nextPC : entry + 14 + 1 = entry + 15 := by omega
  change programStep program before = some after
  rw [fetched program before (entry + 14) (.pop 0) rfl (pcFits 14 (by decide))
    (by simpa [resetPrepareCode] using present ⟨14, by decide⟩)]
  simp only [step, before, resetPrepareConfiguration, running, Bool.false_eq_true,
    ite_false, Fin.reduceEq, ite_true]
  apply congrArg some
  apply resetPrepare_state_eq
  · funext register
    fin_cases register <;> simp only [after, resetPrepareConfiguration, State.advance, State.put,
      Fin.reduceEq, ite_true, ite_false] <;> rfl
  · rfl
  · rfl
  · rfl
  · simp only [after, resetPrepareConfiguration, State.advance, State.put, pcValue, nextPC]
  · change false = state.halted
    exact running.symm

private theorem reset_four_trace (program : Program width 4)
    (s0 s1 s2 s3 s4 : State width 4)
    (t0 : programStep program s0 = some s1) (t1 : programStep program s1 = some s2)
    (t2 : programStep program s2 = some s3) (t3 : programStep program s3 = some s4) :
    Execution program s0 s4 4
      (max s0.liveWords (max s1.liveWords (max s2.liveWords (max s3.liveWords s4.liveWords)))) :=
  Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.refl s4))))

private theorem reset_three_trace (program : Program width 4)
    (s0 s1 s2 s3 : State width 4)
    (t0 : programStep program s0 = some s1) (t1 : programStep program s1 = some s2)
    (t2 : programStep program s2 = some s3) :
    Execution program s0 s3 3
      (max s0.liveWords (max s1.liveWords (max s2.liveWords s3.liveWords))) :=
  Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl s3)))

private theorem reset_prepare_part_0 (program : Program width 4) (state : State width 4)
    (entry table channels nodes count : Nat) (savedBase : Word width) (rest : List (Word width))
    (running : state.halted = false)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? =
      (resetPrepareCode width)[phase.val]?)
    (saved : state.stack = word width (table + (channels + nodes)) :: word width count :: savedBase :: rest) :
    Execution program (resetPrepareConfiguration state (entry + 0) (state.reg 0) (state.reg 1) (state.reg 2) (state.reg 3) (word width (table + (channels + nodes)) :: word width count :: savedBase :: rest)) (resetPrepareConfiguration state (entry + 4) (word width count) (word width 0) (word width (table + (channels + nodes))) savedBase rest) 4 state.liveWords := by
  let s0 := resetPrepareConfiguration state (entry + 0) (state.reg 0) (state.reg 1) (state.reg 2) (state.reg 3) (word width (table + (channels + nodes)) :: word width count :: savedBase :: rest)
  let s1 := resetPrepareConfiguration state (entry + 1) (state.reg 0) (state.reg 1) (word width (table + (channels + nodes))) (state.reg 3) (word width count :: savedBase :: rest)
  let s2 := resetPrepareConfiguration state (entry + 2) (word width count) (state.reg 1) (word width (table + (channels + nodes))) (state.reg 3) (savedBase :: rest)
  let s3 := resetPrepareConfiguration state (entry + 3) (word width count) (state.reg 1) (word width (table + (channels + nodes))) savedBase rest
  let s4 := resetPrepareConfiguration state (entry + 4) (word width count) (word width 0) (word width (table + (channels + nodes))) savedBase rest
  have t0 : programStep program s0 = some s1 :=
    reset_prepare_transition_0 program state entry table channels nodes count savedBase rest running headerRoom channelCell nodeCell scalarRoom capacity present
  have t1 : programStep program s1 = some s2 :=
    reset_prepare_transition_1 program state entry table channels nodes count savedBase rest running headerRoom channelCell nodeCell scalarRoom capacity present
  have t2 : programStep program s2 = some s3 :=
    reset_prepare_transition_2 program state entry table channels nodes count savedBase rest running headerRoom channelCell nodeCell scalarRoom capacity present
  have t3 : programStep program s3 = some s4 :=
    reset_prepare_transition_3 program state entry table channels nodes count savedBase rest running headerRoom channelCell nodeCell scalarRoom capacity present
  have initialLive : state.liveWords = 5 + state.heap.size + (3 + rest.length) + state.output.length := by
    simp only [State.liveWords, saved, List.length_cons]
    omega
  have live0 : s0.liveWords + 0 = state.liveWords := by
    simp only [s0, resetPrepareConfiguration, State.liveWords, List.length_cons]
    simp only [saved, List.length_cons]
  have live1 : s1.liveWords + 1 = state.liveWords := by
    simp only [s1, resetPrepareConfiguration, State.liveWords, List.length_cons]
    simp only [saved, List.length_cons]
    omega
  have live2 : s2.liveWords + 2 = state.liveWords := by
    simp only [s2, resetPrepareConfiguration, State.liveWords, List.length_cons]
    simp only [saved, List.length_cons]
    omega
  have live3 : s3.liveWords + 3 = state.liveWords := by
    simp only [s3, resetPrepareConfiguration, State.liveWords, List.length_cons]
    simp only [saved, List.length_cons]
    omega
  have live4 : s4.liveWords + 3 = state.liveWords := by
    simp only [s4, resetPrepareConfiguration, State.liveWords, List.length_cons]
    simp only [saved, List.length_cons]
    omega
  convert reset_four_trace program s0 s1 s2 s3 s4 t0 t1 t2 t3 using 1
  all_goals omega

private theorem reset_prepare_part_1 (program : Program width 4) (state : State width 4)
    (entry table channels nodes count : Nat) (savedBase : Word width) (rest : List (Word width))
    (running : state.halted = false)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? =
      (resetPrepareCode width)[phase.val]?)
    (saved : state.stack = word width (table + (channels + nodes)) :: word width count :: savedBase :: rest) :
    Execution program (resetPrepareConfiguration state (entry + 4) (word width count) (word width 0) (word width (table + (channels + nodes))) savedBase rest) (resetPrepareConfiguration state (entry + 8) (word width nodes) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)) 4 (state.liveWords - 2) := by
  let s4 := resetPrepareConfiguration state (entry + 4) (word width count) (word width 0) (word width (table + (channels + nodes))) savedBase rest
  let s5 := resetPrepareConfiguration state (entry + 5) (word width count) (word width channels) (word width (table + (channels + nodes))) savedBase rest
  let s6 := resetPrepareConfiguration state (entry + 6) (word width count) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)
  let s7 := resetPrepareConfiguration state (entry + 7) (word width 1) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)
  let s8 := resetPrepareConfiguration state (entry + 8) (word width nodes) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)
  have t4 : programStep program s4 = some s5 :=
    reset_prepare_transition_4 program state entry table channels nodes count savedBase rest running headerRoom channelCell nodeCell scalarRoom capacity present
  have t5 : programStep program s5 = some s6 :=
    reset_prepare_transition_5 program state entry table channels nodes count savedBase rest running headerRoom channelCell nodeCell scalarRoom capacity present
  have t6 : programStep program s6 = some s7 :=
    reset_prepare_transition_6 program state entry table channels nodes count savedBase rest running headerRoom channelCell nodeCell scalarRoom capacity present
  have t7 : programStep program s7 = some s8 :=
    reset_prepare_transition_7 program state entry table channels nodes count savedBase rest running headerRoom channelCell nodeCell scalarRoom capacity present
  have initialLive : state.liveWords = 5 + state.heap.size + (3 + rest.length) + state.output.length := by
    simp only [State.liveWords, saved, List.length_cons]
    omega
  have live4 : s4.liveWords + 3 = state.liveWords := by
    simp only [s4, resetPrepareConfiguration, State.liveWords, List.length_cons]
    simp only [saved, List.length_cons]
    omega
  have live5 : s5.liveWords + 3 = state.liveWords := by
    simp only [s5, resetPrepareConfiguration, State.liveWords, List.length_cons]
    simp only [saved, List.length_cons]
    omega
  have live6 : s6.liveWords + 2 = state.liveWords := by
    simp only [s6, resetPrepareConfiguration, State.liveWords, List.length_cons]
    simp only [saved, List.length_cons]
    omega
  have live7 : s7.liveWords + 2 = state.liveWords := by
    simp only [s7, resetPrepareConfiguration, State.liveWords, List.length_cons]
    simp only [saved, List.length_cons]
    omega
  have live8 : s8.liveWords + 2 = state.liveWords := by
    simp only [s8, resetPrepareConfiguration, State.liveWords, List.length_cons]
    simp only [saved, List.length_cons]
    omega
  convert reset_four_trace program s4 s5 s6 s7 s8 t4 t5 t6 t7 using 1
  all_goals omega

private theorem reset_prepare_part_2 (program : Program width 4) (state : State width 4)
    (entry table channels nodes count : Nat) (savedBase : Word width) (rest : List (Word width))
    (running : state.halted = false)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? =
      (resetPrepareCode width)[phase.val]?)
    (saved : state.stack = word width (table + (channels + nodes)) :: word width count :: savedBase :: rest) :
    Execution program (resetPrepareConfiguration state (entry + 8) (word width nodes) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)) (resetPrepareConfiguration state (entry + 12) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) (word width (table + (channels + nodes))) (word width 1) (word width count :: rest)) 4 (state.liveWords - 2) := by
  let s8 := resetPrepareConfiguration state (entry + 8) (word width nodes) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)
  let s9 := resetPrepareConfiguration state (entry + 9) (word width (channels + nodes)) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)
  let s10 := resetPrepareConfiguration state (entry + 10) (word width (channels + nodes)) (word width channels) (word width (table + (channels + nodes))) (word width (2 ^ width - 1)) (word width count :: rest)
  let s11 := resetPrepareConfiguration state (entry + 11) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) (word width (table + (channels + nodes))) (word width (2 ^ width - 1)) (word width count :: rest)
  let s12 := resetPrepareConfiguration state (entry + 12) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) (word width (table + (channels + nodes))) (word width 1) (word width count :: rest)
  have t8 : programStep program s8 = some s9 :=
    reset_prepare_transition_8 program state entry table channels nodes count savedBase rest running headerRoom channelCell nodeCell scalarRoom capacity present
  have t9 : programStep program s9 = some s10 :=
    reset_prepare_transition_9 program state entry table channels nodes count savedBase rest running headerRoom channelCell nodeCell scalarRoom capacity present
  have t10 : programStep program s10 = some s11 :=
    reset_prepare_transition_10 program state entry table channels nodes count savedBase rest running headerRoom channelCell nodeCell scalarRoom capacity present
  have t11 : programStep program s11 = some s12 :=
    reset_prepare_transition_11 program state entry table channels nodes count savedBase rest running headerRoom channelCell nodeCell scalarRoom capacity present
  have initialLive : state.liveWords = 5 + state.heap.size + (3 + rest.length) + state.output.length := by
    simp only [State.liveWords, saved, List.length_cons]
    omega
  have live8 : s8.liveWords + 2 = state.liveWords := by
    simp only [s8, resetPrepareConfiguration, State.liveWords, List.length_cons]
    simp only [saved, List.length_cons]
    omega
  have live9 : s9.liveWords + 2 = state.liveWords := by
    simp only [s9, resetPrepareConfiguration, State.liveWords, List.length_cons]
    simp only [saved, List.length_cons]
    omega
  have live10 : s10.liveWords + 2 = state.liveWords := by
    simp only [s10, resetPrepareConfiguration, State.liveWords, List.length_cons]
    simp only [saved, List.length_cons]
    omega
  have live11 : s11.liveWords + 2 = state.liveWords := by
    simp only [s11, resetPrepareConfiguration, State.liveWords, List.length_cons]
    simp only [saved, List.length_cons]
    omega
  have live12 : s12.liveWords + 2 = state.liveWords := by
    simp only [s12, resetPrepareConfiguration, State.liveWords, List.length_cons]
    simp only [saved, List.length_cons]
    omega
  convert reset_four_trace program s8 s9 s10 s11 s12 t8 t9 t10 t11 using 1
  all_goals omega

private theorem reset_prepare_part_3 (program : Program width 4) (state : State width 4)
    (entry table channels nodes count : Nat) (savedBase : Word width) (rest : List (Word width))
    (running : state.halted = false)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? =
      (resetPrepareCode width)[phase.val]?)
    (saved : state.stack = word width (table + (channels + nodes)) :: word width count :: savedBase :: rest) :
    Execution program (resetPrepareConfiguration state (entry + 12) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) (word width (table + (channels + nodes))) (word width 1) (word width count :: rest)) (resetPrepareConfiguration state (entry + 15) (word width count) (word width table) (word width (table + (channels + nodes))) (word width 1) rest) 3 (state.liveWords - 2) := by
  let s12 := resetPrepareConfiguration state (entry + 12) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) (word width (table + (channels + nodes))) (word width 1) (word width count :: rest)
  let s13 := resetPrepareConfiguration state (entry + 13) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width channels) (word width (table + (channels + nodes))) (word width 1) (word width count :: rest)
  let s14 := resetPrepareConfiguration state (entry + 14) (word width ((word width (Nat.xor (channels + nodes) (2 ^ width - 1))).val + 1)) (word width table) (word width (table + (channels + nodes))) (word width 1) (word width count :: rest)
  let s15 := resetPrepareConfiguration state (entry + 15) (word width count) (word width table) (word width (table + (channels + nodes))) (word width 1) rest
  have t12 : programStep program s12 = some s13 :=
    reset_prepare_transition_12 program state entry table channels nodes count savedBase rest running headerRoom channelCell nodeCell scalarRoom capacity present
  have t13 : programStep program s13 = some s14 :=
    reset_prepare_transition_13 program state entry table channels nodes count savedBase rest running headerRoom channelCell nodeCell scalarRoom capacity present
  have t14 : programStep program s14 = some s15 :=
    reset_prepare_transition_14 program state entry table channels nodes count savedBase rest running headerRoom channelCell nodeCell scalarRoom capacity present
  have initialLive : state.liveWords = 5 + state.heap.size + (3 + rest.length) + state.output.length := by
    simp only [State.liveWords, saved, List.length_cons]
    omega
  have live12 : s12.liveWords + 2 = state.liveWords := by
    simp only [s12, resetPrepareConfiguration, State.liveWords, List.length_cons]
    simp only [saved, List.length_cons]
    omega
  have live13 : s13.liveWords + 2 = state.liveWords := by
    simp only [s13, resetPrepareConfiguration, State.liveWords, List.length_cons]
    simp only [saved, List.length_cons]
    omega
  have live14 : s14.liveWords + 2 = state.liveWords := by
    simp only [s14, resetPrepareConfiguration, State.liveWords, List.length_cons]
    simp only [saved, List.length_cons]
    omega
  have live15 : s15.liveWords + 3 = state.liveWords := by
    simp only [s15, resetPrepareConfiguration, State.liveWords, List.length_cons]
    simp only [saved, List.length_cons]
    omega
  convert reset_three_trace program s12 s13 s14 s15 t12 t13 t14 using 1
  all_goals omega

theorem reset_prepare_execution (program : Program width 4) (state : State width 4)
    (entry table channels nodes count : Nat) (savedBase : Word width) (rest : List (Word width))
    (running : state.halted = false)
    (headerRoom : 1 < state.heap.size)
    (channelCell : state.heap[0]? = some (word width channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (scalarRoom : table + (channels + nodes) < 2 ^ width)
    (capacity : entry + 15 < 2 ^ width)
    (present : ∀ phase : Fin 15, program[entry + phase.val]? =
      (resetPrepareCode width)[phase.val]?)
    (position : state.pc = word width entry) (saved : state.stack = word width (table + (channels + nodes)) :: word width count :: savedBase :: rest) :
    ∃ final, Execution program state final 15 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = rest ∧ final.output = state.output ∧
      final.reg 0 = word width count ∧ final.reg 1 = word width table ∧
      final.reg 2 = word width (table + (channels + nodes)) ∧ final.reg 3 = word width 1 ∧
      final.pc = word width (entry + 15) ∧ final.halted = false := by
  let s0 := resetPrepareConfiguration state (entry + 0) (state.reg 0) (state.reg 1) (state.reg 2) (state.reg 3) (word width (table + (channels + nodes)) :: word width count :: savedBase :: rest)
  let s4 := resetPrepareConfiguration state (entry + 4) (word width count) (word width 0) (word width (table + (channels + nodes))) savedBase rest
  let s8 := resetPrepareConfiguration state (entry + 8) (word width nodes) (word width channels) (word width (table + (channels + nodes))) savedBase (word width count :: rest)
  let s12 := resetPrepareConfiguration state (entry + 12) (word width (Nat.xor (channels + nodes) (2 ^ width - 1))) (word width channels) (word width (table + (channels + nodes))) (word width 1) (word width count :: rest)
  let s15 := resetPrepareConfiguration state (entry + 15) (word width count) (word width table) (word width (table + (channels + nodes))) (word width 1) rest
  have initialEq : s0 = state := by
    apply resetPrepare_state_eq
    · funext register
      fin_cases register <;> rfl
    · rfl
    · exact saved.symm
    · rfl
    · simpa only [s0, resetPrepareConfiguration, Nat.add_zero] using position.symm
    · rfl
  have part0 : Execution program s0 s4 4 state.liveWords :=
    reset_prepare_part_0 program state entry table channels nodes count savedBase rest running headerRoom channelCell nodeCell scalarRoom capacity present saved
  have part1 : Execution program s4 s8 4 (state.liveWords - 2) :=
    reset_prepare_part_1 program state entry table channels nodes count savedBase rest running headerRoom channelCell nodeCell scalarRoom capacity present saved
  have part2 : Execution program s8 s12 4 (state.liveWords - 2) :=
    reset_prepare_part_2 program state entry table channels nodes count savedBase rest running headerRoom channelCell nodeCell scalarRoom capacity present saved
  have part3 : Execution program s12 s15 3 (state.liveWords - 2) :=
    reset_prepare_part_3 program state entry table channels nodes count savedBase rest running headerRoom channelCell nodeCell scalarRoom capacity present saved
  have whole : Execution program state s15 15 state.liveWords := by
    rw [initialEq] at part0
    convert ((part0.append part1).append part2).append part3 using 1
    all_goals omega
  refine ⟨s15, whole, rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl, running⟩
  all_goals rfl


/-- A complete touched-slot reset restores the same once-allocated dictionary
for the next root, without clearing or copying the source packet. -/
theorem reset_empty_dictionary (heap : Array (Word width))
    (layout : ForestZeroDictionary.Layout ambient heap.size)
    (dictionary : Dictionary ambient) (represented : Represented heap layout dictionary)
    (ambientFits : ambient ≤ 2 ^ width) :
    Represented
      (Controller.Cost.ForestZeroReset.resetHeap width layout.tableBase layout.inverseBase heap
        dictionary.coordinates.size)
      { tableBase := layout.tableBase
        inverseBase := layout.inverseBase
        tableBound := by simpa only [Controller.Cost.ForestZeroReset.resetHeap_size] using layout.tableBound
        inverseBound := by simpa only [Controller.Cost.ForestZeroReset.resetHeap_size] using layout.inverseBound
        disjoint := layout.disjoint }
      (ForestZeroCompile.empty ambient) := by
  refine ⟨ForestZeroCompile.empty_coherent ambient, ?_, ?_⟩
  · intro coordinate
    simpa [ForestZeroCompile.empty] using
      Controller.Cost.ForestZeroReset.reset_slots_zero heap layout dictionary represented ambientFits coordinate
  · intro index coordinate allocated
    simp only [ForestZeroCompile.empty, Array.getElem?_empty] at allocated
    cases allocated

/-- An actual touched-prefix reset preserves every source word preceding the
shared table; inverse reads remain valid throughout the recurrence. -/
private theorem reset_source_cell (heap : Array (Word width))
    (layout : ForestZeroDictionary.Layout ambient heap.size)
    (coordinates : Array (Fin ambient)) (countBound : coordinates.size ≤ ambient)
    (stored : Controller.Cost.ForestZeroReset.InverseStored heap layout.inverseBase coordinates)
    (ambientFits : ambient ≤ 2 ^ width) (count : Nat) (remaining : count ≤ coordinates.size)
    (address : Nat) (below : address < layout.tableBase) :
    (Controller.Cost.ForestZeroReset.resetHeap width layout.tableBase layout.inverseBase heap count)[address]? =
      heap[address]? := by
  induction count generalizing heap with
  | zero => rfl
  | succ count ih =>
      let current : Fin coordinates.size := ⟨count, by omega⟩
      let coordinate : Fin ambient := coordinates[count]'current.isLt
      have actual := Controller.Cost.ForestZeroReset.inverse_read heap layout.inverseBase
        coordinates stored current ambientFits
      change (heap[layout.inverseBase + count]?.getD (word width 0)).val = coordinate.val at actual
      rw [Controller.Cost.ForestZeroReset.resetHeap, actual]
      let cleared := heap.setIfInBounds (layout.tableBase + coordinate.val) (word width 0)
      let nextLayout : ForestZeroDictionary.Layout ambient cleared.size :=
        { tableBase := layout.tableBase
          inverseBase := layout.inverseBase
          tableBound := by simpa [cleared] using layout.tableBound
          inverseBound := by simpa [cleared] using layout.inverseBound
          disjoint := layout.disjoint }
      have nextStored := Controller.Cost.ForestZeroReset.clear_inverse heap layout coordinates
        countBound stored coordinate
      have recursive := ih cleared nextLayout nextStored (by omega)
      exact (recursive below).trans
        (Controller.Cost.ForestZeroReset.clear_outside heap layout.tableBase coordinate address
          (Or.inl below))

/-- Reset restores the shared zero dictionary while retaining the loaded source. -/
theorem reset_source_prefix (heap : Array (Word width))
    (layout : ForestZeroDictionary.Layout ambient heap.size)
    (dictionary : Dictionary ambient) (represented : Represented heap layout dictionary)
    (ambientFits : ambient ≤ 2 ^ width) :
    Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase heap
      (Controller.Cost.ForestZeroReset.resetHeap width layout.tableBase layout.inverseBase heap
        dictionary.coordinates.size) := by
  refine ⟨by have := layout.tableBound; omega,
    by rw [Controller.Cost.ForestZeroReset.resetHeap_size]; have := layout.tableBound; omega, ?_⟩
  intro address below
  exact reset_source_cell heap layout dictionary.coordinates
    (ForestZeroDictionary.count_le_ambient dictionary represented.coherent)
    represented.inverse ambientFits dictionary.coordinates.size (Nat.le_refl _) address below


/-- Recover the actual inverse/count/base stack words, derive the shared table
from original headers, and run the touched-only reset in the same caller. -/
theorem retained_dictionary_reset_execution (program : Program width 8)
    (state : State width 8) (entry channels nodes : Nat)
    (dictionary : Dictionary ambient) (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : Represented state.heap layout dictionary)
    (ambientEq : ambient = channels + nodes)
    (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (tablePositive : 0 < layout.tableBase)
    (savedBase : Word width) (rest : List (Word width))
    (saved : state.stack = word width layout.inverseBase ::
      word width dictionary.coordinates.size :: savedBase :: rest)
    (position : state.pc = word width entry) (running : state.halted = false)
    (channelsCell : state.heap[0]? = some (word width channels))
    (nodesCell : state.heap[1]? = some (word width nodes))
    (headerRoom : 1 < state.heap.size) (heapFits : state.heap.size < 2 ^ width)
    (capacity : entry + 27 < 2 ^ width)
    (prepareAt : ForestZeroCallerWiden.WidenedBlockAt program entry (resetPrepareCode width).toList)
    (resetAt : ForestZeroCallerWiden.WidenedBlockAt program (entry + 15)
      (Controller.Cost.ForestZeroReset.code width (entry + 15))) :
    ∃ final, Execution program state final (12 * dictionary.coordinates.size + 16) state.liveWords ∧
      final.heap = Controller.Cost.ForestZeroReset.resetHeap width layout.tableBase
        layout.inverseBase state.heap dictionary.coordinates.size ∧
      final.stack = rest ∧ final.output = state.output ∧
      final.pc = word width (entry + 27) ∧ final.halted = false ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase state.heap final.heap ∧
      (∀ coordinate : Fin ambient, final.heap[layout.tableBase + coordinate.val]? =
        some (word width 0)) := by
  let lowState : State width 4 :=
    { reg := fun register => state.reg (Controller.Cost.RegisterWiden.widenRegister register)
      heap := state.heap, stack := state.stack, output := state.output,
      pc := state.pc, halted := state.halted }
  have initialEq : Controller.Cost.RegisterWiden.widenState lowState state.reg = state := by
    apply projection_state_eq
    · funext register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have inverseScalar : layout.inverseBase = layout.tableBase + (channels + nodes) :=
    adjacent.trans (congrArg (fun value => layout.tableBase + value) ambientEq)
  have scalarRoom : layout.tableBase + (channels + nodes) < 2 ^ width := by
    have := layout.inverseBound
    omega
  have lowSaved : lowState.stack = word width (layout.tableBase + (channels + nodes)) ::
      word width dictionary.coordinates.size :: savedBase :: rest := by
    simpa only [lowState, inverseScalar] using saved
  have lowPrepare : ∀ phase : Fin 15,
      (ForestZeroCallerWiden.lowerProgram program)[entry + phase.val]? =
        (resetPrepareCode width)[phase.val]? := by
    intro phase
    have found := ForestZeroCallerWiden.lower_block program entry
      (resetPrepareCode width).toList prepareAt phase.val
      (by change phase.val < 15; exact phase.isLt)
    simpa only [Array.getElem?_toList] using found
  obtain ⟨prepared, first, preparedHeap, preparedStack, preparedOutput,
      prepared0, prepared1, prepared2, prepared3, preparedPC, preparedRunning⟩ :=
    reset_prepare_execution (ForestZeroCallerWiden.lowerProgram program) lowState entry
      layout.tableBase channels nodes dictionary.coordinates.size savedBase rest running
      headerRoom channelsCell nodesCell scalarRoom (by omega) lowPrepare position lowSaved
  have preparedEq : prepared = Controller.Cost.ForestZeroTouch.atState state.heap (entry + 15)
      dictionary.coordinates.size layout.tableBase layout.inverseBase 1 rest state.output := by
    apply resetPrepare_state_eq
    · funext register
      fin_cases register
      · exact prepared0
      · exact prepared1
      · change prepared.reg 2 = word width layout.inverseBase
        simpa only [inverseScalar] using prepared2
      · exact prepared3
    · exact preparedHeap
    · exact preparedStack
    · exact preparedOutput
    · exact preparedPC
    · exact preparedRunning
  have countBound := ForestZeroDictionary.count_le_ambient dictionary represented.coherent
  have ambientFits : ambient + 1 < 2 ^ width := by
    have := layout.tableBound
    omega
  have second := Controller.Cost.ForestZeroReset.reset_execution
    (ForestZeroCallerWiden.lowerProgram program) state.heap layout dictionary.coordinates countBound
    represented.inverse (entry + 15) 1 dictionary.coordinates.size rest state.output
    (Nat.le_refl _) heapFits ambientFits (by omega)
    (ForestZeroCallerWiden.lower_block program (entry + 15)
      (Controller.Cost.ForestZeroReset.code width (entry + 15)) resetAt)
  rw [preparedEq] at first
  let finalLow := Controller.Cost.ForestZeroTouch.atState
    (Controller.Cost.ForestZeroReset.resetHeap width layout.tableBase layout.inverseBase state.heap
      dictionary.coordinates.size) ((entry + 15) + 12) 0 layout.tableBase layout.inverseBase
      (if dictionary.coordinates.size = 0 then 1 else 0) rest state.output
  have lowRun : Execution (ForestZeroCallerWiden.lowerProgram program) lowState finalLow
      (12 * dictionary.coordinates.size + 16) lowState.liveWords := by
    have initialLive : lowState.liveWords = 5 + state.heap.size + (3 + rest.length) + state.output.length := by
      simp only [lowState, State.liveWords, saved, List.length_cons]
      omega
    convert first.append second using 1
    · omega
    · rw [initialLive]
      split_ifs <;> omega
  have actual := ForestZeroCallerWiden.execution program lowState finalLow
    (12 * dictionary.coordinates.size + 16) lowState.liveWords lowRun rfl state.reg
  let final := Controller.Cost.RegisterWiden.widenState finalLow state.reg
  have initialLive : lowState.liveWords + 4 = state.liveWords := by
    unfold State.liveWords
    simp only [lowState]
    omega
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, rfl, ?_, ?_⟩
  · simpa only [initialEq, initialLive] using actual
  · simp only [final, Controller.Cost.RegisterWiden.widenState_pc,
      finalLow, Controller.Cost.ForestZeroTouch.atState]
  · exact reset_source_prefix state.heap layout dictionary represented (by omega)
  · intro coordinate
    exact Controller.Cost.ForestZeroReset.reset_slots_zero state.heap layout dictionary
      represented (by omega) coordinate


theorem initialized_original_projection_charged_execution {channels ambient : Nat}
    (dictionary : Dictionary ambient) (keep : Nat)
    (formula : Controller.CNF.Formula (Fin dictionary.coordinates.size)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex (formula.clauses.toList) recordStart recordEnd base
      (Controller.Horn.IndexScan.occurrences (formula.clauses.toList) recordStart).length state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Controller.Horn.WorklistMark.Stored ([] : List (Fin dictionary.coordinates.size)) base state.heap)
    (separated : base + 5 * dictionary.coordinates.size + 4 ≤ recordStart)
    (setupAt : ∀ phase : Fin 10, program[entry + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := dictionary.coordinates.size) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := dictionary.coordinates.size) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size < 2 ^ width) (setupCapacity : entry + 10 < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : keep ≤ state.heap.size) (prefixBelow : keep ≤ base)
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := dictionary.coordinates.size) width base fetch)[phase.val]?)
    (headCapacity : seedDone + 4 < 2 ^ width)
    (fifoDone bucket advance ready skip : Nat)
    (fetchAt : Controller.Horn.WorklistFIFO.FetchAt (n := dictionary.coordinates.size) program base fetch fifoDone bucket)
    (advanceAt : Controller.Horn.WorklistFIFO.AdvanceAt (n := dictionary.coordinates.size) program base advance fetch)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program bucket advance ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := dictionary.coordinates.size) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (projectionEntry cleanupEntry returnPc : Nat)
    (successAt : Controller.Cost.ForestZeroAnswer.At program fifoDone 1 projectionEntry)
    (conflictAt : Controller.Cost.ForestZeroAnswer.At program conflict 0 cleanupEntry)
    (successCapacity : fifoDone + 4 < 2 ^ width)
    (conflictCapacity : conflict + 4 < 2 ^ width)
    (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : Represented state.heap layout dictionary)
    (nodes count : Nat)
    (ambientEq : ambient = channels + nodes)
    (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (tableBefore : layout.tableBase + ambient ≤ keep)
    (inverseBefore : layout.inverseBase + ambient ≤ keep)
    (headersBefore : 1 < keep)
    (channelsCell : state.heap[0]? = some (word width channels))
    (nodesCell : state.heap[1]? = some (word width nodes))
    (localFit : dictionary.coordinates.size + 1 < 2 ^ width)
    (channelsFit : channels + 1 < 2 ^ width) (offRoom : base + 1 < 2 ^ width)
    (projectionCapacity : projectionEntry + 35 < 2 ^ width)
    (constantsAt : ∀ phase : Fin 2, program[projectionEntry + phase.val]? =
      (projectionConstantsCode width)[phase.val]?)
    (preparationAt : ∀ phase : Fin 19, program[projectionEntry + 2 + phase.val]? =
      (channelPrepareCode width)[phase.val]?)
    (emitAt : Controller.Cost.ForestZeroChannelEmit.CodeAt program (projectionEntry + 21) cleanupEntry)
    (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (cleanupLoop : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width) (countFits : count < 2 ^ width)
    (rest : List (Word width))
    (savedCount : state.stack = word width count :: word width layout.inverseBase ::
      word width dictionary.coordinates.size :: word width base :: rest)
    (allocated : state.heap.size = keep + count) :
    ∃ answer : Bool, ∃ queue final ticks peak,
      Execution program state final ticks peak ∧
      ticks ≤ 36 * formula.clauses.toList.length +
        32 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length +
        26 * dictionary.coordinates.size + 4 * count +
        (if answer then 13 * channels + 54 else 32) ∧
      peak ≤ state.liveWords + channels + 1 ∧ final.heap.size = keep ∧
      final.stack = word width layout.inverseBase :: word width dictionary.coordinates.size ::
        word width base :: rest ∧
      final.output = (if answer then (List.finRange channels).map (fun channel =>
        Controller.Cost.ForestZeroChannelEmit.bitWord width
          (ForestZeroModelLift.lift dictionary true
            (Controller.Cost.ForestZeroChannelEmit.localValues queue)
            ⟨channel.val, by rw [ambientEq]; have := channel.isLt; omega⟩)) ++
          word width 1 :: state.output else word width 0 :: state.output) ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame keep state.heap final.heap ∧
      (answer = true ↔ ∃ assignment, Controller.CNF.Satisfies assignment formula) ∧
      (answer = true → Controller.CNF.Satisfies (Controller.Horn.WorklistOutcome.offAssignment queue) formula ∧
        Controller.Horn.WorklistOutcome.offAssignment queue = Controller.Horn.greatestCandidate formula)
 := by
  obtain ⟨queue, middle, firstTicks, firstBound, first, middleSize,
      middleStack, middleOutput, firstFrame, outcome⟩ :=
    Controller.Cost.ForestZeroOutcome.initialized_original_execution keep formula dual
      recordHeader recordStart recordEnd base entry scan seedDone conflict state program
      physical header fifo separated setupAt scanAt position running zero one room
      setupCapacity scanCapacity prefixBound prefixBelow fetch headAt headCapacity
      fifoDone bucket advance ready skip fetchAt advanceAt loopAt readyAt
      fetchCapacity advanceCapacity bucketCapacity readyCapacity
  have middleLive : middle.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [middleSize, middleStack, middleOutput]
  rcases outcome with ⟨pc, live, noModels⟩ | ⟨fired, finished, model, forced⟩
  · obtain ⟨tagged, tagTrace, tagHeap, tagStack, tagOutput, tagPC, tagRunning, tagFrame⟩ :=
      Controller.Cost.ForestZeroAnswer.execution keep program conflict 0 cleanupEntry middle
        conflictAt pc live conflictCapacity (by omega) (by rw [middleSize]; exact prefixBound)
    let savedRest := word width layout.inverseBase :: word width dictionary.coordinates.size ::
      word width base :: rest
    obtain ⟨final, cleanup, finalSize, finalStack, finalOutput, finalPC, finalRunning, lastFrame⟩ :=
      Controller.Cost.ForestZeroReclaim.stacked_execution program cleanupEntry returnPc keep count
        tagged savedRest cleanupSetup cleanupLoop tagPC tagRunning cleanupCapacity countFits
        (tagStack.trans (middleStack.trans savedCount))
        (by rw [tagHeap, middleSize]; exact allocated)
    have taggedLive : tagged.liveWords = state.liveWords + 1 := by
      unfold State.liveWords
      rw [tagHeap, middleSize, tagStack, middleStack, tagOutput, middleOutput]
      simp only [List.length_cons]
      omega
    refine ⟨false, queue, final, firstTicks + 4 + (4 * count + 4),
      max state.liveWords (max (middle.liveWords + 1) tagged.liveWords),
      (by simpa only [Nat.add_assoc] using first.append (tagTrace.append cleanup)),
      (by simp only [Bool.false_eq_true, ite_false]; omega), ?_, finalSize, finalStack,
      ?_, finalPC, finalRunning,
      Controller.Cost.ForestZeroBackendFrame.trans firstFrame
        (Controller.Cost.ForestZeroBackendFrame.trans tagFrame lastFrame), ?_, ?_⟩
    · rw [middleLive, taggedLive]
      omega
    · simpa only [Bool.false_eq_true, ite_false, savedRest, tagOutput, middleOutput] using finalOutput
    · constructor
      · intro impossible
        cases impossible
      · intro possible
        exact False.elim (noModels possible)
    · intro impossible
      cases impossible
  · obtain ⟨tagged, tagTrace, tagHeap, tagStack, tagOutput, tagPC, tagRunning, tagFrame⟩ :=
      Controller.Cost.ForestZeroAnswer.execution keep program fifoDone 1 projectionEntry middle
        successAt finished.position finished.running successCapacity (by omega)
        (by rw [middleSize]; exact prefixBound)
    have taggedFrame := Controller.Cost.ForestZeroBackendFrame.trans firstFrame tagFrame
    let taggedLayout := retainedDictionaryLayout state.heap tagged.heap keep layout taggedFrame
      tableBefore inverseBefore
    have taggedDictionary : Represented tagged.heap taggedLayout dictionary :=
      dictionary_prefix_transport state.heap tagged.heap keep layout dictionary represented
        taggedFrame tableBefore inverseBefore
    have taggedFifo : Controller.Horn.WorklistMark.Stored queue base tagged.heap := by
      simpa only [tagHeap] using finished.fifo
    obtain ⟨channelsStored, nodesStored⟩ := projection_headers_transport state.heap tagged.heap
      keep channels nodes taggedFrame headersBefore channelsCell nodesCell
    obtain ⟨final, lastTicks, lastPeak, suffix, suffixTime, suffixSpace, finalSize, finalStack,
        finalOutput, finalPC, finalRunning, suffixFrame⟩ :=
      terminal_dictionary_emission_reclaim program tagged projectionEntry cleanupEntry returnPc
        base keep count nodes dictionary taggedLayout taggedDictionary ambientEq adjacent queue taggedFifo
        localFit tagPC tagRunning channelsStored nodesStored
        (by have := taggedFrame.2.1; omega) channelsFit (by rw [tagHeap, middleSize]; exact room)
        offRoom projectionCapacity constantsAt preparationAt emitAt cleanupSetup cleanupLoop
        cleanupCapacity countFits rest (tagStack.trans (middleStack.trans savedCount))
        (by rw [tagHeap, middleSize]; exact allocated) tableBefore inverseBefore
    have taggedLive : tagged.liveWords = state.liveWords + 1 := by
      unfold State.liveWords
      rw [tagHeap, middleSize, tagStack, middleStack, tagOutput, middleOutput]
      simp only [List.length_cons]
      omega
    refine ⟨true, queue, final, firstTicks + 4 + lastTicks,
      max state.liveWords (max (middle.liveWords + 1) lastPeak),
      (by simpa only [Nat.add_assoc] using first.append (tagTrace.append suffix)),
      (by simp only [ite_true]; omega), ?_, finalSize, finalStack,
      ?_, finalPC, finalRunning,
      Controller.Cost.ForestZeroBackendFrame.trans taggedFrame suffixFrame,
      ⟨fun _ => ⟨Controller.Horn.WorklistOutcome.offAssignment queue, model⟩, fun _ => rfl⟩,
      fun _ => ⟨model, Controller.Cost.ForestZeroAnswerReclaim.terminal_greatest formula dual
        queue model forced⟩⟩
    · rw [taggedLive] at suffixSpace
      rw [middleLive]
      omega
    · simpa only [ite_true, tagOutput, middleOutput] using finalOutput



theorem original_projection_reset_execution {channels ambient : Nat}
    (dictionary : Dictionary ambient) (keep : Nat)
    (formula : Controller.CNF.Formula (Fin dictionary.coordinates.size)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex (formula.clauses.toList) recordStart recordEnd base
      (Controller.Horn.IndexScan.occurrences (formula.clauses.toList) recordStart).length state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Controller.Horn.WorklistMark.Stored ([] : List (Fin dictionary.coordinates.size)) base state.heap)
    (separated : base + 5 * dictionary.coordinates.size + 4 ≤ recordStart)
    (setupAt : ∀ phase : Fin 10, program[entry + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := dictionary.coordinates.size) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := dictionary.coordinates.size) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size < 2 ^ width) (setupCapacity : entry + 10 < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : keep ≤ state.heap.size) (prefixBelow : keep ≤ base)
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := dictionary.coordinates.size) width base fetch)[phase.val]?)
    (headCapacity : seedDone + 4 < 2 ^ width)
    (fifoDone bucket advance ready skip : Nat)
    (fetchAt : Controller.Horn.WorklistFIFO.FetchAt (n := dictionary.coordinates.size) program base fetch fifoDone bucket)
    (advanceAt : Controller.Horn.WorklistFIFO.AdvanceAt (n := dictionary.coordinates.size) program base advance fetch)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program bucket advance ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := dictionary.coordinates.size) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (projectionEntry cleanupEntry returnPc : Nat)
    (successAt : Controller.Cost.ForestZeroAnswer.At program fifoDone 1 projectionEntry)
    (conflictAt : Controller.Cost.ForestZeroAnswer.At program conflict 0 cleanupEntry)
    (successCapacity : fifoDone + 4 < 2 ^ width)
    (conflictCapacity : conflict + 4 < 2 ^ width)
    (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : Represented state.heap layout dictionary)
    (nodes count : Nat)
    (ambientEq : ambient = channels + nodes)
    (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (tableBefore : layout.tableBase + ambient ≤ keep)
    (inverseBefore : layout.inverseBase + ambient ≤ keep)
    (headersBefore : 1 < keep)
    (channelsCell : state.heap[0]? = some (word width channels))
    (nodesCell : state.heap[1]? = some (word width nodes))
    (localFit : dictionary.coordinates.size + 1 < 2 ^ width)
    (channelsFit : channels + 1 < 2 ^ width) (offRoom : base + 1 < 2 ^ width)
    (projectionCapacity : projectionEntry + 35 < 2 ^ width)
    (constantsAt : ∀ phase : Fin 2, program[projectionEntry + phase.val]? =
      (projectionConstantsCode width)[phase.val]?)
    (preparationAt : ∀ phase : Fin 19, program[projectionEntry + 2 + phase.val]? =
      (channelPrepareCode width)[phase.val]?)
    (emitAt : Controller.Cost.ForestZeroChannelEmit.CodeAt program (projectionEntry + 21) cleanupEntry)
    (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (cleanupLoop : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width) (countFits : count < 2 ^ width)
    (rest : List (Word width))
    (savedCount : state.stack = word width count :: word width layout.inverseBase ::
      word width dictionary.coordinates.size :: word width base :: rest)
    (allocated : state.heap.size = keep + count)
    (tablePositive : 0 < layout.tableBase)
    (resetCapacity : returnPc + 27 < 2 ^ width)
    (resetPrepareAt : ForestZeroCallerWiden.WidenedBlockAt program returnPc (resetPrepareCode width).toList)
    (resetLoopAt : ForestZeroCallerWiden.WidenedBlockAt program (returnPc + 15)
      (Controller.Cost.ForestZeroReset.code width (returnPc + 15))) :
    ∃ answer : Bool, ∃ queue final ticks peak,
      Execution program state final ticks peak ∧
      ticks ≤ 36 * formula.clauses.toList.length +
        32 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length +
        38 * dictionary.coordinates.size + 4 * count +
        (if answer then 13 * channels + 70 else 48) ∧
      peak ≤ state.liveWords + channels + 1 ∧
      final.heap.size = keep ∧ final.stack = rest ∧
      final.output = (if answer then (List.finRange channels).map (fun channel =>
        Controller.Cost.ForestZeroChannelEmit.bitWord width
          (ForestZeroModelLift.lift dictionary true
            (Controller.Cost.ForestZeroChannelEmit.localValues queue)
            ⟨channel.val, by rw [ambientEq]; have := channel.isLt; omega⟩)) ++
          word width 1 :: state.output else word width 0 :: state.output) ∧
      final.pc = word width (returnPc + 27) ∧ final.halted = false ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase state.heap final.heap ∧
      (∀ coordinate : Fin ambient, final.heap[layout.tableBase + coordinate.val]? = some (word width 0)) ∧
      (answer = true ↔ ∃ assignment, Controller.CNF.Satisfies assignment formula) ∧
      (answer = true → Controller.CNF.Satisfies (Controller.Horn.WorklistOutcome.offAssignment queue) formula ∧
        Controller.Horn.WorklistOutcome.offAssignment queue = Controller.Horn.greatestCandidate formula) := by
  obtain ⟨answer, queue, reclaimed, firstTicks, firstPeak, first, timeBound, spaceBound,
      reclaimedSize, reclaimedStack, reclaimedOutput, reclaimedPC, reclaimedRunning,
      reclaimedFrame, meaning, greatest⟩ :=
    initialized_original_projection_charged_execution dictionary keep formula dual
      recordHeader recordStart recordEnd base entry scan seedDone conflict state program
      physical header fifo separated setupAt scanAt position running zero one room
      setupCapacity scanCapacity prefixBound prefixBelow fetch headAt headCapacity fifoDone
      bucket advance ready skip fetchAt advanceAt loopAt readyAt fetchCapacity advanceCapacity
      bucketCapacity readyCapacity projectionEntry cleanupEntry returnPc successAt conflictAt
      successCapacity conflictCapacity layout represented nodes count ambientEq adjacent
      tableBefore inverseBefore headersBefore channelsCell nodesCell localFit channelsFit
      offRoom projectionCapacity constantsAt preparationAt emitAt cleanupSetup cleanupLoop
      cleanupCapacity countFits rest savedCount allocated
  let reclaimedLayout := retainedDictionaryLayout state.heap reclaimed.heap keep layout
    reclaimedFrame tableBefore inverseBefore
  have reclaimedDictionary : Represented reclaimed.heap reclaimedLayout dictionary :=
    dictionary_prefix_transport state.heap reclaimed.heap keep layout dictionary represented
      reclaimedFrame tableBefore inverseBefore
  obtain ⟨channelHeader, nodeHeader⟩ := projection_headers_transport state.heap reclaimed.heap
    keep channels nodes reclaimedFrame headersBefore channelsCell nodesCell
  obtain ⟨final, reset, finalHeap, finalStack, finalOutput, finalPC, finalRunning,
      resetFrame, zeroSlots⟩ :=
    retained_dictionary_reset_execution program reclaimed returnPc channels nodes dictionary
      reclaimedLayout reclaimedDictionary ambientEq adjacent tablePositive (word width base)
      rest reclaimedStack reclaimedPC reclaimedRunning channelHeader nodeHeader
      (by rw [reclaimedSize]; exact headersBefore)
      (by rw [reclaimedSize]; omega) resetCapacity resetPrepareAt resetLoopAt
  have sourceBound : layout.tableBase ≤ keep := by omega
  have sourceFrame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase
      state.heap reclaimed.heap :=
    ⟨by omega, by rw [reclaimedSize]; omega,
      fun address below => reclaimedFrame.2.2 address (lt_of_lt_of_le below sourceBound)⟩
  have reclaimedLive : reclaimed.liveWords ≤ firstPeak := first.final_storage_le
  refine ⟨answer, queue, final, firstTicks + (12 * dictionary.coordinates.size + 16),
    max firstPeak reclaimed.liveWords, first.append reset, ?_, ?_, ?_, finalStack,
    finalOutput.trans reclaimedOutput, finalPC, finalRunning,
    Controller.Cost.ForestZeroBackendFrame.trans sourceFrame resetFrame, zeroSlots,
    meaning, greatest⟩
  · cases answer <;> simp only [Bool.false_eq_true, ite_false, ite_true] at timeBound ⊢ <;> omega
  · omega
  · rw [finalHeap, Controller.Cost.ForestZeroReset.resetHeap_size, reclaimedSize]

/-- The saved decision word is physically restored after touched-slot reset.
The following root dispatcher reads register four, while the caller stack is
restored exactly. -/
theorem decision_recover_execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (tag : Word width) (rest : List (Word width))
    (saved : state.stack = tag :: rest) (position : state.pc = word width entry)
    (running : state.halted = false) (capacity : entry + 1 < 2 ^ width)
    (present : program[entry]? = some (.pop 4)) :
    ∃ final, Execution program state final 1 state.liveWords ∧
      final.reg 4 = tag ∧ final.heap = state.heap ∧ final.stack = rest ∧
      final.output = state.output ∧ final.pc = word width (entry + 1) ∧
      final.halted = false ∧ (∀ register, register ≠ 4 → final.reg register = state.reg register) := by
  let final : State width 8 := { state.advance.put 4 tag with stack := rest }
  have actual : programStep program state = some final := by
    rw [fetched8 program state entry (.pop 4) position (by omega) present]
    simp only [step, running, Bool.false_eq_true, ite_false, saved]
    rfl
  have finalLe : final.liveWords ≤ state.liveWords := by
    simp only [final, State.put, State.advance, State.liveWords, saved, List.length_cons]
    omega
  refine ⟨final, ?_, ?_, rfl, rfl, rfl, ?_, running, ?_⟩
  · simpa only [Nat.add_zero, Nat.max_eq_left finalLe] using
      Execution.cons actual (Execution.refl final)
  · simp only [final, State.put, Fin.reduceEq, ite_true]
  · have entryValue : (word width entry).val = entry := Nat.mod_eq_of_lt (by omega)
    simp only [final, State.put, State.advance, position, entryValue]
  · intro register different
    simp only [final, State.put, State.advance, ite_eq_right different]

theorem retained_dictionary_reset_registers_execution (program : Program width 8)
    (state : State width 8) (entry channels nodes : Nat)
    (dictionary : Dictionary ambient) (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : Represented state.heap layout dictionary)
    (ambientEq : ambient = channels + nodes)
    (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (tablePositive : 0 < layout.tableBase)
    (savedBase : Word width) (rest : List (Word width))
    (saved : state.stack = word width layout.inverseBase ::
      word width dictionary.coordinates.size :: savedBase :: rest)
    (position : state.pc = word width entry) (running : state.halted = false)
    (channelsCell : state.heap[0]? = some (word width channels))
    (nodesCell : state.heap[1]? = some (word width nodes))
    (headerRoom : 1 < state.heap.size) (heapFits : state.heap.size < 2 ^ width)
    (capacity : entry + 27 < 2 ^ width)
    (prepareAt : ForestZeroCallerWiden.WidenedBlockAt program entry (resetPrepareCode width).toList)
    (resetAt : ForestZeroCallerWiden.WidenedBlockAt program (entry + 15)
      (Controller.Cost.ForestZeroReset.code width (entry + 15))) :
    ∃ final, Execution program state final (12 * dictionary.coordinates.size + 16) state.liveWords ∧
      final.heap = Controller.Cost.ForestZeroReset.resetHeap width layout.tableBase
        layout.inverseBase state.heap dictionary.coordinates.size ∧
      final.stack = rest ∧ final.output = state.output ∧
      final.pc = word width (entry + 27) ∧ final.halted = false ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase state.heap final.heap ∧
      (∀ coordinate : Fin ambient, final.heap[layout.tableBase + coordinate.val]? =
        some (word width 0)) ∧
      final.reg 0 = word width 0 ∧ final.reg 1 = word width layout.tableBase ∧
      final.reg 2 = word width layout.inverseBase := by
  let lowState : State width 4 :=
    { reg := fun register => state.reg (Controller.Cost.RegisterWiden.widenRegister register)
      heap := state.heap, stack := state.stack, output := state.output,
      pc := state.pc, halted := state.halted }
  have initialEq : Controller.Cost.RegisterWiden.widenState lowState state.reg = state := by
    apply projection_state_eq
    · funext register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have inverseScalar : layout.inverseBase = layout.tableBase + (channels + nodes) :=
    adjacent.trans (congrArg (fun value => layout.tableBase + value) ambientEq)
  have scalarRoom : layout.tableBase + (channels + nodes) < 2 ^ width := by
    have := layout.inverseBound
    omega
  have lowSaved : lowState.stack = word width (layout.tableBase + (channels + nodes)) ::
      word width dictionary.coordinates.size :: savedBase :: rest := by
    simpa only [lowState, inverseScalar] using saved
  have lowPrepare : ∀ phase : Fin 15,
      (ForestZeroCallerWiden.lowerProgram program)[entry + phase.val]? =
        (resetPrepareCode width)[phase.val]? := by
    intro phase
    have found := ForestZeroCallerWiden.lower_block program entry
      (resetPrepareCode width).toList prepareAt phase.val
      (by change phase.val < 15; exact phase.isLt)
    simpa only [Array.getElem?_toList] using found
  obtain ⟨prepared, first, preparedHeap, preparedStack, preparedOutput,
      prepared0, prepared1, prepared2, prepared3, preparedPC, preparedRunning⟩ :=
    reset_prepare_execution (ForestZeroCallerWiden.lowerProgram program) lowState entry
      layout.tableBase channels nodes dictionary.coordinates.size savedBase rest running
      headerRoom channelsCell nodesCell scalarRoom (by omega) lowPrepare position lowSaved
  have preparedEq : prepared = Controller.Cost.ForestZeroTouch.atState state.heap (entry + 15)
      dictionary.coordinates.size layout.tableBase layout.inverseBase 1 rest state.output := by
    apply resetPrepare_state_eq
    · funext register
      fin_cases register
      · exact prepared0
      · exact prepared1
      · change prepared.reg 2 = word width layout.inverseBase
        simpa only [inverseScalar] using prepared2
      · exact prepared3
    · exact preparedHeap
    · exact preparedStack
    · exact preparedOutput
    · exact preparedPC
    · exact preparedRunning
  have countBound := ForestZeroDictionary.count_le_ambient dictionary represented.coherent
  have ambientFits : ambient + 1 < 2 ^ width := by
    have := layout.tableBound
    omega
  have second := Controller.Cost.ForestZeroReset.reset_execution
    (ForestZeroCallerWiden.lowerProgram program) state.heap layout dictionary.coordinates countBound
    represented.inverse (entry + 15) 1 dictionary.coordinates.size rest state.output
    (Nat.le_refl _) heapFits ambientFits (by omega)
    (ForestZeroCallerWiden.lower_block program (entry + 15)
      (Controller.Cost.ForestZeroReset.code width (entry + 15)) resetAt)
  rw [preparedEq] at first
  let finalLow := Controller.Cost.ForestZeroTouch.atState
    (Controller.Cost.ForestZeroReset.resetHeap width layout.tableBase layout.inverseBase state.heap
      dictionary.coordinates.size) ((entry + 15) + 12) 0 layout.tableBase layout.inverseBase
      (if dictionary.coordinates.size = 0 then 1 else 0) rest state.output
  have lowRun : Execution (ForestZeroCallerWiden.lowerProgram program) lowState finalLow
      (12 * dictionary.coordinates.size + 16) lowState.liveWords := by
    have initialLive : lowState.liveWords = 5 + state.heap.size + (3 + rest.length) + state.output.length := by
      simp only [lowState, State.liveWords, saved, List.length_cons]
      omega
    convert first.append second using 1
    · omega
    · rw [initialLive]
      split_ifs <;> omega
  have actual := ForestZeroCallerWiden.execution program lowState finalLow
    (12 * dictionary.coordinates.size + 16) lowState.liveWords lowRun rfl state.reg
  let final := Controller.Cost.RegisterWiden.widenState finalLow state.reg
  have initialLive : lowState.liveWords + 4 = state.liveWords := by
    unfold State.liveWords
    simp only [lowState]
    omega
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, rfl, ?_, ?_, rfl, rfl, rfl⟩
  · simpa only [initialEq, initialLive] using actual
  · simp only [final, Controller.Cost.RegisterWiden.widenState_pc,
      finalLow, Controller.Cost.ForestZeroTouch.atState]
  · exact reset_source_prefix state.heap layout dictionary represented (by omega)
  · intro coordinate
    exact Controller.Cost.ForestZeroReset.reset_slots_zero state.heap layout dictionary
      represented (by omega) coordinate



theorem initialized_original_saved_projection_execution {channels ambient : Nat}
    (dictionary : Dictionary ambient) (keep : Nat)
    (formula : Controller.CNF.Formula (Fin dictionary.coordinates.size)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex (formula.clauses.toList) recordStart recordEnd base
      (Controller.Horn.IndexScan.occurrences (formula.clauses.toList) recordStart).length state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Controller.Horn.WorklistMark.Stored ([] : List (Fin dictionary.coordinates.size)) base state.heap)
    (separated : base + 5 * dictionary.coordinates.size + 4 ≤ recordStart)
    (setupAt : ∀ phase : Fin 10, program[entry + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := dictionary.coordinates.size) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := dictionary.coordinates.size) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size < 2 ^ width) (setupCapacity : entry + 10 < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : keep ≤ state.heap.size) (prefixBelow : keep ≤ base)
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := dictionary.coordinates.size) width base fetch)[phase.val]?)
    (headCapacity : seedDone + 4 < 2 ^ width)
    (fifoDone bucket advance ready skip : Nat)
    (fetchAt : Controller.Horn.WorklistFIFO.FetchAt (n := dictionary.coordinates.size) program base fetch fifoDone bucket)
    (advanceAt : Controller.Horn.WorklistFIFO.AdvanceAt (n := dictionary.coordinates.size) program base advance fetch)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program bucket advance ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := dictionary.coordinates.size) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (projectionEntry cleanupEntry returnPc : Nat)
    (successAt : Controller.Cost.ForestZeroAnswer.SavedAt program fifoDone 1 projectionEntry)
    (conflictAt : Controller.Cost.ForestZeroAnswer.SavedAt program conflict 0 cleanupEntry)
    (successCapacity : fifoDone + 13 < 2 ^ width)
    (conflictCapacity : conflict + 13 < 2 ^ width)
    (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : Represented state.heap layout dictionary)
    (nodes count : Nat)
    (ambientEq : ambient = channels + nodes)
    (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (tableBefore : layout.tableBase + ambient ≤ keep)
    (inverseBefore : layout.inverseBase + ambient ≤ keep)
    (headersBefore : 1 < keep)
    (channelsCell : state.heap[0]? = some (word width channels))
    (nodesCell : state.heap[1]? = some (word width nodes))
    (localFit : dictionary.coordinates.size + 1 < 2 ^ width)
    (channelsFit : channels + 1 < 2 ^ width) (offRoom : base + 1 < 2 ^ width)
    (projectionCapacity : projectionEntry + 35 < 2 ^ width)
    (constantsAt : ∀ phase : Fin 2, program[projectionEntry + phase.val]? =
      (projectionConstantsCode width)[phase.val]?)
    (preparationAt : ∀ phase : Fin 19, program[projectionEntry + 2 + phase.val]? =
      (channelPrepareCode width)[phase.val]?)
    (emitAt : Controller.Cost.ForestZeroChannelEmit.CodeAt program (projectionEntry + 21) cleanupEntry)
    (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (cleanupLoop : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width) (countFits : count < 2 ^ width)
    (rest : List (Word width))
    (savedCount : state.stack = word width count :: word width layout.inverseBase ::
      word width dictionary.coordinates.size :: word width base :: rest)
    (allocated : state.heap.size = keep + count) :
    ∃ answer : Bool, ∃ queue final ticks peak,
      Execution program state final ticks peak ∧
      ticks ≤ 36 * formula.clauses.toList.length +
        32 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length +
        26 * dictionary.coordinates.size + 4 * count +
        (if answer then 13 * channels + 63 else 41) ∧
      peak ≤ state.liveWords + channels + 2 ∧ final.heap.size = keep ∧
      final.stack = word width layout.inverseBase :: word width dictionary.coordinates.size ::
        word width base :: word width (if answer then 1 else 0) :: rest ∧
      final.output = (if answer then (List.finRange channels).map (fun channel =>
        Controller.Cost.ForestZeroChannelEmit.bitWord width
          (ForestZeroModelLift.lift dictionary true
            (Controller.Cost.ForestZeroChannelEmit.localValues queue)
            ⟨channel.val, by rw [ambientEq]; have := channel.isLt; omega⟩)) ++
          word width 1 :: state.output else word width 0 :: state.output) ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame keep state.heap final.heap ∧
      (answer = true ↔ ∃ assignment, Controller.CNF.Satisfies assignment formula) ∧
      (answer = true → Controller.CNF.Satisfies (Controller.Horn.WorklistOutcome.offAssignment queue) formula ∧
        Controller.Horn.WorklistOutcome.offAssignment queue = Controller.Horn.greatestCandidate formula)
 := by
  obtain ⟨queue, middle, firstTicks, firstBound, first, middleSize,
      middleStack, middleOutput, firstFrame, outcome⟩ :=
    Controller.Cost.ForestZeroOutcome.initialized_original_execution keep formula dual
      recordHeader recordStart recordEnd base entry scan seedDone conflict state program
      physical header fifo separated setupAt scanAt position running zero one room
      setupCapacity scanCapacity prefixBound prefixBelow fetch headAt headCapacity
      fifoDone bucket advance ready skip fetchAt advanceAt loopAt readyAt
      fetchCapacity advanceCapacity bucketCapacity readyCapacity
  have middleLive : middle.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [middleSize, middleStack, middleOutput]
  rcases outcome with ⟨pc, live, noModels⟩ | ⟨fired, finished, model, forced⟩
  · obtain ⟨tagged, tagTrace, tagHeap, tagOutput, tagStack, tagFive, tagPC, tagRunning⟩ :=
      Controller.Cost.ForestZeroAnswer.saved_execution program middle conflict 0 cleanupEntry
        (word width count) (word width layout.inverseBase)
        (word width dictionary.coordinates.size) (word width base) rest
        (middleStack.trans savedCount) pc live conflictCapacity conflictAt
    have tagFrame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame keep middle.heap tagged.heap := by
      simpa only [tagHeap] using Controller.Cost.ForestZeroBackendFrame.refl middle.heap
        (by rw [middleSize]; exact prefixBound)
    let savedRest := word width layout.inverseBase :: word width dictionary.coordinates.size ::
      word width base :: word width 0 :: rest
    obtain ⟨final, cleanup, finalSize, finalStack, finalOutput, finalPC, finalRunning, lastFrame⟩ :=
      Controller.Cost.ForestZeroReclaim.stacked_execution program cleanupEntry returnPc keep count
        tagged savedRest cleanupSetup cleanupLoop tagPC tagRunning cleanupCapacity countFits
        (by simpa only [savedRest] using tagStack)
        (by rw [tagHeap, middleSize]; exact allocated)
    have taggedLive : tagged.liveWords = state.liveWords + 2 := by
      unfold State.liveWords
      rw [tagHeap, middleSize, tagStack, tagOutput, middleOutput, savedCount]
      simp only [List.length_cons]
      omega
    refine ⟨false, queue, final, firstTicks + 13 + (4 * count + 4),
      max state.liveWords (max (middle.liveWords + 2) tagged.liveWords),
      (by simpa only [Nat.add_assoc] using first.append (tagTrace.append cleanup)),
      (by simp only [Bool.false_eq_true, ite_false]; omega), ?_, finalSize, finalStack,
      ?_, finalPC, finalRunning,
      Controller.Cost.ForestZeroBackendFrame.trans firstFrame
        (Controller.Cost.ForestZeroBackendFrame.trans tagFrame lastFrame), ?_, ?_⟩
    · rw [middleLive, taggedLive]
      omega
    · simpa only [Bool.false_eq_true, ite_false, savedRest, tagOutput, middleOutput] using finalOutput
    · constructor
      · intro impossible
        cases impossible
      · intro possible
        exact False.elim (noModels possible)
    · intro impossible
      cases impossible
  · obtain ⟨tagged, tagTrace, tagHeap, tagOutput, tagStack, tagFive, tagPC, tagRunning⟩ :=
      Controller.Cost.ForestZeroAnswer.saved_execution program middle fifoDone 1 projectionEntry
        (word width count) (word width layout.inverseBase)
        (word width dictionary.coordinates.size) (word width base) rest
        (middleStack.trans savedCount) finished.position finished.running successCapacity successAt
    have tagFrame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame keep middle.heap tagged.heap := by
      simpa only [tagHeap] using Controller.Cost.ForestZeroBackendFrame.refl middle.heap
        (by rw [middleSize]; exact prefixBound)
    have taggedFrame := Controller.Cost.ForestZeroBackendFrame.trans firstFrame tagFrame
    let taggedLayout := retainedDictionaryLayout state.heap tagged.heap keep layout taggedFrame
      tableBefore inverseBefore
    have taggedDictionary : Represented tagged.heap taggedLayout dictionary :=
      dictionary_prefix_transport state.heap tagged.heap keep layout dictionary represented
        taggedFrame tableBefore inverseBefore
    have taggedFifo : Controller.Horn.WorklistMark.Stored queue base tagged.heap := by
      simpa only [tagHeap] using finished.fifo
    obtain ⟨channelsStored, nodesStored⟩ := projection_headers_transport state.heap tagged.heap
      keep channels nodes taggedFrame headersBefore channelsCell nodesCell
    obtain ⟨final, lastTicks, lastPeak, suffix, suffixTime, suffixSpace, finalSize, finalStack,
        finalOutput, finalPC, finalRunning, suffixFrame⟩ :=
      terminal_dictionary_emission_reclaim program tagged projectionEntry cleanupEntry returnPc
        base keep count nodes dictionary taggedLayout taggedDictionary ambientEq adjacent queue taggedFifo
        localFit tagPC tagRunning channelsStored nodesStored
        (by have := taggedFrame.2.1; omega) channelsFit (by rw [tagHeap, middleSize]; exact room)
        offRoom projectionCapacity constantsAt preparationAt emitAt cleanupSetup cleanupLoop
        cleanupCapacity countFits (word width 1 :: rest) tagStack
        (by rw [tagHeap, middleSize]; exact allocated) tableBefore inverseBefore
    have taggedLive : tagged.liveWords = state.liveWords + 2 := by
      unfold State.liveWords
      rw [tagHeap, middleSize, tagStack, tagOutput, middleOutput, savedCount]
      simp only [List.length_cons]
      omega
    refine ⟨true, queue, final, firstTicks + 13 + lastTicks,
      max state.liveWords (max (middle.liveWords + 2) lastPeak),
      (by simpa only [Nat.add_assoc] using first.append (tagTrace.append suffix)),
      (by simp only [ite_true]; omega), ?_, finalSize, finalStack,
      ?_, finalPC, finalRunning,
      Controller.Cost.ForestZeroBackendFrame.trans taggedFrame suffixFrame,
      ⟨fun _ => ⟨Controller.Horn.WorklistOutcome.offAssignment queue, model⟩, fun _ => rfl⟩,
      fun _ => ⟨model, Controller.Cost.ForestZeroAnswerReclaim.terminal_greatest formula dual
        queue model forced⟩⟩
    · rw [taggedLive] at suffixSpace
      rw [middleLive]
      omega
    · simpa only [ite_true, tagOutput, middleOutput] using finalOutput




theorem original_saved_projection_reset_execution {channels ambient : Nat}
    (dictionary : Dictionary ambient) (keep : Nat)
    (formula : Controller.CNF.Formula (Fin dictionary.coordinates.size)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex (formula.clauses.toList) recordStart recordEnd base
      (Controller.Horn.IndexScan.occurrences (formula.clauses.toList) recordStart).length state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Controller.Horn.WorklistMark.Stored ([] : List (Fin dictionary.coordinates.size)) base state.heap)
    (separated : base + 5 * dictionary.coordinates.size + 4 ≤ recordStart)
    (setupAt : ∀ phase : Fin 10, program[entry + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := dictionary.coordinates.size) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := dictionary.coordinates.size) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size < 2 ^ width) (setupCapacity : entry + 10 < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : keep ≤ state.heap.size) (prefixBelow : keep ≤ base)
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := dictionary.coordinates.size) width base fetch)[phase.val]?)
    (headCapacity : seedDone + 4 < 2 ^ width)
    (fifoDone bucket advance ready skip : Nat)
    (fetchAt : Controller.Horn.WorklistFIFO.FetchAt (n := dictionary.coordinates.size) program base fetch fifoDone bucket)
    (advanceAt : Controller.Horn.WorklistFIFO.AdvanceAt (n := dictionary.coordinates.size) program base advance fetch)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program bucket advance ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := dictionary.coordinates.size) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (projectionEntry cleanupEntry returnPc : Nat)
    (successAt : Controller.Cost.ForestZeroAnswer.SavedAt program fifoDone 1 projectionEntry)
    (conflictAt : Controller.Cost.ForestZeroAnswer.SavedAt program conflict 0 cleanupEntry)
    (successCapacity : fifoDone + 13 < 2 ^ width)
    (conflictCapacity : conflict + 13 < 2 ^ width)
    (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : Represented state.heap layout dictionary)
    (nodes count : Nat)
    (ambientEq : ambient = channels + nodes)
    (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (tableBefore : layout.tableBase + ambient ≤ keep)
    (inverseBefore : layout.inverseBase + ambient ≤ keep)
    (headersBefore : 1 < keep)
    (channelsCell : state.heap[0]? = some (word width channels))
    (nodesCell : state.heap[1]? = some (word width nodes))
    (localFit : dictionary.coordinates.size + 1 < 2 ^ width)
    (channelsFit : channels + 1 < 2 ^ width) (offRoom : base + 1 < 2 ^ width)
    (projectionCapacity : projectionEntry + 35 < 2 ^ width)
    (constantsAt : ∀ phase : Fin 2, program[projectionEntry + phase.val]? =
      (projectionConstantsCode width)[phase.val]?)
    (preparationAt : ∀ phase : Fin 19, program[projectionEntry + 2 + phase.val]? =
      (channelPrepareCode width)[phase.val]?)
    (emitAt : Controller.Cost.ForestZeroChannelEmit.CodeAt program (projectionEntry + 21) cleanupEntry)
    (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (cleanupLoop : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width) (countFits : count < 2 ^ width)
    (rest : List (Word width))
    (savedCount : state.stack = word width count :: word width layout.inverseBase ::
      word width dictionary.coordinates.size :: word width base :: rest)
    (allocated : state.heap.size = keep + count)
    (tablePositive : 0 < layout.tableBase)
    (resetCapacity : returnPc + 27 < 2 ^ width)
    (resetPrepareAt : ForestZeroCallerWiden.WidenedBlockAt program returnPc (resetPrepareCode width).toList)
    (resetLoopAt : ForestZeroCallerWiden.WidenedBlockAt program (returnPc + 15)
      (Controller.Cost.ForestZeroReset.code width (returnPc + 15)))
    (decisionCapacity : returnPc + 28 < 2 ^ width)
    (decisionAt : program[returnPc + 27]? = some (.pop 4)) :
    ∃ answer : Bool, ∃ queue final ticks peak,
      Execution program state final ticks peak ∧
      ticks ≤ 36 * formula.clauses.toList.length +
        32 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length +
        38 * dictionary.coordinates.size + 4 * count +
        (if answer then 13 * channels + 80 else 58) ∧
      peak ≤ state.liveWords + channels + 2 ∧
      final.heap.size = keep ∧ final.stack = rest ∧
      final.output = (if answer then (List.finRange channels).map (fun channel =>
        Controller.Cost.ForestZeroChannelEmit.bitWord width
          (ForestZeroModelLift.lift dictionary true
            (Controller.Cost.ForestZeroChannelEmit.localValues queue)
            ⟨channel.val, by rw [ambientEq]; have := channel.isLt; omega⟩)) ++
          word width 1 :: state.output else word width 0 :: state.output) ∧
      final.pc = word width (returnPc + 28) ∧ final.halted = false ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase state.heap final.heap ∧
      (∀ coordinate : Fin ambient, final.heap[layout.tableBase + coordinate.val]? = some (word width 0)) ∧
      final.reg 4 = word width (if answer then 1 else 0) ∧
      final.reg 0 = word width 0 ∧ final.reg 1 = word width layout.tableBase ∧
      final.reg 2 = word width layout.inverseBase ∧
      (answer = true ↔ ∃ assignment, Controller.CNF.Satisfies assignment formula) ∧
      (answer = true → Controller.CNF.Satisfies (Controller.Horn.WorklistOutcome.offAssignment queue) formula ∧
        Controller.Horn.WorklistOutcome.offAssignment queue = Controller.Horn.greatestCandidate formula) := by
  obtain ⟨answer, queue, reclaimed, firstTicks, firstPeak, first, timeBound, spaceBound,
      reclaimedSize, reclaimedStack, reclaimedOutput, reclaimedPC, reclaimedRunning,
      reclaimedFrame, meaning, greatest⟩ :=
    initialized_original_saved_projection_execution dictionary keep formula dual
      recordHeader recordStart recordEnd base entry scan seedDone conflict state program
      physical header fifo separated setupAt scanAt position running zero one room
      setupCapacity scanCapacity prefixBound prefixBelow fetch headAt headCapacity fifoDone
      bucket advance ready skip fetchAt advanceAt loopAt readyAt fetchCapacity advanceCapacity
      bucketCapacity readyCapacity projectionEntry cleanupEntry returnPc successAt conflictAt
      successCapacity conflictCapacity layout represented nodes count ambientEq adjacent
      tableBefore inverseBefore headersBefore channelsCell nodesCell localFit channelsFit
      offRoom projectionCapacity constantsAt preparationAt emitAt cleanupSetup cleanupLoop
      cleanupCapacity countFits rest savedCount allocated
  let reclaimedLayout := retainedDictionaryLayout state.heap reclaimed.heap keep layout
    reclaimedFrame tableBefore inverseBefore
  have reclaimedDictionary : Represented reclaimed.heap reclaimedLayout dictionary :=
    dictionary_prefix_transport state.heap reclaimed.heap keep layout dictionary represented
      reclaimedFrame tableBefore inverseBefore
  obtain ⟨channelHeader, nodeHeader⟩ := projection_headers_transport state.heap reclaimed.heap
    keep channels nodes reclaimedFrame headersBefore channelsCell nodesCell
  obtain ⟨resetFinal, reset, finalHeap, finalStack, finalOutput, finalPC, finalRunning,
      resetFrame, zeroSlots, finalZero, finalTable, finalInverse⟩ :=
    retained_dictionary_reset_registers_execution program reclaimed returnPc channels nodes dictionary
      reclaimedLayout reclaimedDictionary ambientEq adjacent tablePositive (word width base)
      (word width (if answer then 1 else 0) :: rest) reclaimedStack reclaimedPC reclaimedRunning channelHeader nodeHeader
      (by rw [reclaimedSize]; exact headersBefore)
      (by rw [reclaimedSize]; omega) resetCapacity resetPrepareAt resetLoopAt
  have sourceBound : layout.tableBase ≤ keep := by omega
  have sourceFrame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase
      state.heap reclaimed.heap :=
    ⟨by omega, by rw [reclaimedSize]; omega,
      fun address below => reclaimedFrame.2.2 address (lt_of_lt_of_le below sourceBound)⟩
  have reclaimedLive : reclaimed.liveWords ≤ firstPeak := first.final_storage_le
  obtain ⟨final, recover, decision, recoverHeap, recoverStack, recoverOutput, recoverPC,
      recoverRunning, recoverRegisters⟩ :=
    decision_recover_execution program resetFinal (returnPc + 27)
      (word width (if answer then 1 else 0)) rest finalStack finalPC finalRunning
      (by omega) decisionAt
  have resetLive : resetFinal.liveWords ≤ reclaimed.liveWords := reset.final_storage_le
  have recoverFrame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase
      resetFinal.heap final.heap := by
    simpa only [recoverHeap] using Controller.Cost.ForestZeroBackendFrame.refl resetFinal.heap
      (by rw [finalHeap, Controller.Cost.ForestZeroReset.resetHeap_size, reclaimedSize]; omega)
  refine ⟨answer, queue, final, firstTicks + (12 * dictionary.coordinates.size + 16) + 1,
    max (max firstPeak reclaimed.liveWords) resetFinal.liveWords,
    (first.append reset).append recover, ?_, ?_, ?_, recoverStack,
    recoverOutput.trans (finalOutput.trans reclaimedOutput), ?_, recoverRunning,
    Controller.Cost.ForestZeroBackendFrame.trans sourceFrame
      (Controller.Cost.ForestZeroBackendFrame.trans resetFrame recoverFrame),
    ?_, decision, ?_, ?_, ?_, meaning, greatest⟩
  · cases answer <;> simp only [Bool.false_eq_true, ite_false, ite_true] at timeBound ⊢ <;> omega
  · omega
  · rw [recoverHeap, finalHeap, Controller.Cost.ForestZeroReset.resetHeap_size, reclaimedSize]
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using recoverPC
  · have tableScalar : reclaimedLayout.tableBase = layout.tableBase := rfl
    simpa only [recoverHeap, tableScalar] using zeroSlots
  · exact (recoverRegisters 0 (by decide)).trans finalZero
  · exact (recoverRegisters 1 (by decide)).trans finalTable
  · exact (recoverRegisters 2 (by decide)).trans finalInverse


theorem scratch_indexed_original_reuse_execution {channels ambient : Nat}
    (dictionary : Dictionary ambient) (keep : Nat)
    (formula : Controller.CNF.Formula (Fin dictionary.coordinates.size)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (backend : Controller.Horn.SourceDirectory.Layout formula.clauses.toList)
    (sourceStored : Stored formula.clauses.toList backend.directory backend.source state.heap)
    (directoryCursor : CursorStored backend.directory backend.directoryHeader state.heap)
    (directoryEnd : CursorStored (backend.directory + 2 * formula.clauses.toList.length) backend.endHeader state.heap)
    (baseEq : backend.base = state.heap.size) (recordHeaderEq : backend.recordHeader = keep)
    (headerEq : recordHeader = backend.recordHeader) (backendBaseEq : base = backend.base)
    (recordStartEq : recordStart = state.heap.size + 5 * dictionary.coordinates.size + 4)
    (recordEndEq : recordEnd = Controller.Horn.NormalizeLoop.recordOffset formula.clauses.toList
      recordStart formula.clauses.toList.length)
    (localCount : state.reg 2 = word width dictionary.coordinates.size)
    (sourcePointer : state.reg 1 = word width state.heap.size)
    (countAt : ∀ phase : Fin 11, program[entry + phase.val]? = (scratchCountCode width)[phase.val]?)
    (allocateAt : Controller.Horn.TrackedAllocate.CodeAt program (entry + 11))
    (headersAt : ∀ phase : Fin 15, program[entry + 16 + phase.val]? = (scratchHeaderCode width)[phase.val]?)
    (endpointAt : ∀ phase : Fin 5, program[entry + 31 + phase.val]? = (scratchEndpointCode (width := width))[phase.val]?)
    (saveAt : ∀ phase : Fin 6, program[entry + 36 + phase.val]? = (saveProjectionCode (width := width))[phase.val]?)
    (normalizerAt : Controller.Horn.NormalizeLoop.CodeAt program (entry + 42) formula.clauses.toList backend)
    (headersAbove : ∀ address ∈ [backend.recordHeader, backend.inputHeader, backend.firstHeader,
      backend.directoryHeader, backend.endHeader], backend.recordHeader ≤ address)
    (indexSaveAt : Controller.Cost.ForestZeroHeaderBridge.SaveAt program (entry + 203) recordHeader)
    (indexAt : Controller.Horn.IndexScan.At (n := dictionary.coordinates.size) program (entry + 210) base recordStart)
    (indexRestoreAt : Controller.Cost.ForestZeroHeaderBridge.RestoreAt program (entry + 242))
    (captureAt : ∀ phase : Fin 6, program[entry + 245 + phase.val]? = (Controller.Cost.ForestZeroReclaim.captureCode width)[phase.val]?)
    (fullCapacity : entry + 261 < 2 ^ width)
    (setupAt : ∀ phase : Fin 10, program[entry + 251 + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := dictionary.coordinates.size) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := dictionary.coordinates.size) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : state.heap.size + 5 * dictionary.coordinates.size + 4 +
      3 * formula.clauses.toList.length + (formula.clauses.toList.map List.length).sum +
      2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : keep ≤ state.heap.size) (prefixBelow : keep ≤ base)
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := dictionary.coordinates.size) width base fetch)[phase.val]?)
    (headCapacity : seedDone + 4 < 2 ^ width)
    (fifoDone bucket advance ready skip : Nat)
    (fetchAt : Controller.Horn.WorklistFIFO.FetchAt (n := dictionary.coordinates.size) program base fetch fifoDone bucket)
    (advanceAt : Controller.Horn.WorklistFIFO.AdvanceAt (n := dictionary.coordinates.size) program base advance fetch)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program bucket advance ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := dictionary.coordinates.size) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (projectionEntry cleanupEntry returnPc : Nat)
    (successAt : Controller.Cost.ForestZeroAnswer.SavedAt program fifoDone 1 projectionEntry)
    (conflictAt : Controller.Cost.ForestZeroAnswer.SavedAt program conflict 0 cleanupEntry)
    (successCapacity : fifoDone + 13 < 2 ^ width)
    (conflictCapacity : conflict + 13 < 2 ^ width)
    (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : Represented state.heap layout dictionary)
    (nodes : Nat)
    (ambientEq : ambient = channels + nodes)
    (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (tableBefore : layout.tableBase + ambient ≤ keep)
    (inverseBefore : layout.inverseBase + ambient ≤ keep)
    (headersBefore : 1 < keep)
    (channelsCell : state.heap[0]? = some (word width channels))
    (nodesCell : state.heap[1]? = some (word width nodes))
    (localFit : dictionary.coordinates.size + 1 < 2 ^ width)
    (channelsFit : channels + 1 < 2 ^ width) (offRoom : base + 1 < 2 ^ width)
    (projectionCapacity : projectionEntry + 35 < 2 ^ width)
    (constantsAt : ∀ phase : Fin 2, program[projectionEntry + phase.val]? =
      (projectionConstantsCode width)[phase.val]?)
    (preparationAt : ∀ phase : Fin 19, program[projectionEntry + 2 + phase.val]? =
      (channelPrepareCode width)[phase.val]?)
    (emitAt : Controller.Cost.ForestZeroChannelEmit.CodeAt program (projectionEntry + 21) cleanupEntry)
    (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (cleanupLoop : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width)
    (rest : List (Word width))
    (saved : state.stack = word width layout.inverseBase :: word width keep :: rest)
    (tablePositive : 0 < layout.tableBase)
    (resetCapacity : returnPc + 27 < 2 ^ width)
    (resetPrepareAt : ForestZeroCallerWiden.WidenedBlockAt program returnPc (resetPrepareCode width).toList)
    (resetLoopAt : ForestZeroCallerWiden.WidenedBlockAt program (returnPc + 15)
      (Controller.Cost.ForestZeroReset.code width (returnPc + 15)))
    (decisionCapacity : returnPc + 28 < 2 ^ width)
    (decisionAt : program[returnPc + 27]? = some (.pop 4)) :
    ∃ answer : Bool, ∃ queue final ticks peak,
      Execution program state final ticks peak ∧
      ticks ≤ 63 * dictionary.coordinates.size +
        61 * (formula.clauses.toList.map List.length).sum + 125 * formula.clauses.toList.length +
        48 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length +
        4 * (recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length - keep) +
        (if answer then 13 * channels + 166 else 144) ∧
      peak ≤ state.liveWords + 5 * dictionary.coordinates.size +
        3 * formula.clauses.toList.length + (formula.clauses.toList.map List.length).sum +
        2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length + channels + 8 ∧
      final.heap.size = keep ∧ final.stack = rest ∧
      final.output = (if answer then (List.finRange channels).map (fun channel =>
        Controller.Cost.ForestZeroChannelEmit.bitWord width
          (ForestZeroModelLift.lift dictionary true
            (Controller.Cost.ForestZeroChannelEmit.localValues queue)
            ⟨channel.val, by rw [ambientEq]; have := channel.isLt; omega⟩)) ++
          word width 1 :: state.output else word width 0 :: state.output) ∧
      final.pc = word width (returnPc + 28) ∧ final.halted = false ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase state.heap final.heap ∧
      (∀ coordinate : Fin ambient, final.heap[layout.tableBase + coordinate.val]? = some (word width 0)) ∧
      final.reg 4 = word width (if answer then 1 else 0) ∧
      final.reg 0 = word width 0 ∧ final.reg 1 = word width layout.tableBase ∧
      final.reg 2 = word width layout.inverseBase ∧
      (answer = true ↔ ∃ assignment, Controller.CNF.Satisfies assignment formula) ∧
      (answer = true → Controller.CNF.Satisfies (Controller.Horn.WorklistOutcome.offAssignment queue) formula ∧
        Controller.Horn.WorklistOutcome.offAssignment queue = Controller.Horn.greatestCandidate formula) := by
  let incidences := (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length
  let count := recordEnd + 2 * incidences - keep
  have dualRows : ∀ index : Fin formula.clauses.toList.length, Controller.Horn.DualHornClause formula.clauses.toList[index.val] := by
    intro index
    apply dual
    have member := List.getElem_mem index.isLt
    simpa only [Array.mem_toList_iff] using member
  obtain ⟨normalized, marks, normalizeTicks, normalizePeak, normalizeTrace, complete,
      normalizedPC, normalizeTime, normalizeSpace, normalizedStack, normalizedOutput,
      normalizeFrame⟩ :=
    scratch_normalized_execution program state entry formula.clauses.toList backend sourceStored directoryCursor
      directoryEnd baseEq position running localCount sourcePointer layout.inverseBase rest
      (by simpa only [recordHeaderEq] using saved) (by omega) (by omega)
      countAt allocateAt headersAt endpointAt saveAt normalizerAt dualRows headersAbove
  have completed : Controller.Horn.NormalizeLoop.Invariant formula.clauses.toList backend recordStart formula.clauses.toList.length marks normalized := by
    simpa only [← recordStartEq] using complete
  have normalizedSize : normalized.heap.size = recordEnd := by
    exact completed.records.endpoint.trans recordEndEq.symm
  have endBound : recordEnd ≤ recordStart + 3 * formula.clauses.toList.length + (formula.clauses.toList.map List.length).sum := by
    have sumBound := Controller.Horn.NormalizeLoop.wordSuffix_bound formula.clauses.toList 0
    simp only [Controller.Horn.NormalizeLoop.wordSuffix, Controller.Horn.NormalizeLoop.literalSuffix,
      List.drop_zero] at sumBound
    rw [recordEndEq, Controller.Horn.NormalizeLoop.recordOffset, List.take_length]
    omega
  have keepFrame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame keep state.heap normalized.heap := by
    simpa only [recordHeaderEq] using normalizeFrame
  obtain ⟨physical, cursor, fifo⟩ := Controller.Cost.ForestZeroIndexMarks.normalized_inputs
    formula.clauses.toList backend recordStart marks normalized completed
  have baseBelow : base ≤ normalized.heap.size := by
    have lower := Controller.Horn.NormalizeLoop.recordOffset_above formula.clauses.toList recordStart formula.clauses.toList.length
    rw [← recordEndEq, ← normalizedSize] at lower
    omega
  have headerBelow : recordHeader < base := by
    have headerBound := backend.headersBefore backend.recordHeader (by simp)
    have directoryBound := backend.directoryBefore
    have sourceBound := backend.sourceBefore
    unfold Controller.Horn.SourceDirectory.sourceOffset at sourceBound
    omega
  let savedRest := word width layout.inverseBase :: word width dictionary.coordinates.size ::
    word width base :: rest
  obtain ⟨indexed, indexTrace, indexedPhysical, indexedHeader, indexedFIFO, indexedFrame,
      indexedSize, allocated, indexedStack, indexedOutput, indexedZero, indexedOne,
      indexedPC, indexedRunning⟩ :=
    Controller.Cost.ForestZeroIndexMarks.indexed_capture_inputs keep program formula.clauses.toList
      (entry + 203) recordHeader recordStart recordEnd base normalized indexSaveAt
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using indexAt)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using indexRestoreAt)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using captureAt)
      (by simpa only [normalizedSize, backendBaseEq] using physical)
      (by simpa only [normalizedSize, headerEq] using cursor)
      normalizedPC completed.input.running completed.input.zero completed.input.one
      (by omega) baseBelow headerBelow prefixBelow
      (by simpa only [backendBaseEq] using fifo) (by omega)
      (by rw [normalizedSize]; omega) savedRest
      (by simpa only [savedRest, backendBaseEq, baseEq, recordHeaderEq] using normalizedStack)
  have indexKeepFrame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame keep normalized.heap indexed.heap :=
    ⟨by omega, by have := indexedFrame.2.1; omega,
      fun address below => indexedFrame.2.2 address (lt_of_lt_of_le below prefixBelow)⟩
  have prefixFrame := Controller.Cost.ForestZeroBackendFrame.trans keepFrame indexKeepFrame
  let indexedLayout := retainedDictionaryLayout state.heap indexed.heap keep layout prefixFrame
    tableBefore inverseBefore
  have indexedInverse : indexedLayout.inverseBase = layout.inverseBase := rfl
  have indexedTable : indexedLayout.tableBase = layout.tableBase := rfl
  have indexedDictionary : Represented indexed.heap indexedLayout dictionary :=
    dictionary_prefix_transport state.heap indexed.heap keep layout dictionary represented prefixFrame
      tableBefore inverseBefore
  obtain ⟨indexedChannels, indexedNodes⟩ := projection_headers_transport state.heap indexed.heap keep
    channels nodes prefixFrame headersBefore channelsCell nodesCell
  have actualSize : indexed.heap.size = keep + count := by
    simpa only [count, incidences, normalizedSize] using allocated
  have indexedLive : indexed.liveWords = normalized.liveWords + 2 * incidences := by
    unfold State.liveWords
    rw [indexedSize, indexedStack, indexedOutput, normalizedStack]
    simp only [savedRest, List.length_cons, List.length_nil]
    omega
  obtain ⟨answer, queue, final, terminalTicks, terminalPeak, terminalTrace, terminalTime,
      terminalSpace, finalSize, finalStack, finalOutput, finalPC, finalRunning, terminalFrame,
      zeroSlots, decision, finalZero, finalTable, finalInverse, meaning, greatest⟩ :=
    original_saved_projection_reset_execution dictionary keep formula dual recordHeader recordStart recordEnd
      base (entry + 251) scan seedDone conflict indexed program indexedPhysical indexedHeader indexedFIFO
      (by simpa only [backendBaseEq] using completed.recordsAbove) setupAt scanAt (by simpa only [Nat.add_assoc, Nat.reduceAdd] using indexedPC) indexedRunning
      indexedZero indexedOne (by rw [indexedSize, normalizedSize]; omega) (by omega) scanCapacity
      (by have := prefixFrame.2.1; omega) prefixBelow fetch headAt headCapacity fifoDone bucket advance
      ready skip fetchAt advanceAt loopAt readyAt fetchCapacity advanceCapacity bucketCapacity readyCapacity
      projectionEntry cleanupEntry returnPc successAt conflictAt successCapacity conflictCapacity
      indexedLayout indexedDictionary nodes count ambientEq adjacent tableBefore inverseBefore headersBefore
      indexedChannels indexedNodes localFit channelsFit offRoom projectionCapacity constantsAt preparationAt
      emitAt cleanupSetup cleanupLoop cleanupCapacity (by unfold count; omega) rest
      (by simpa only [count, incidences, normalizedSize, savedRest, indexedInverse] using indexedStack)
      actualSize tablePositive resetCapacity resetPrepareAt resetLoopAt decisionCapacity decisionAt
  rw [indexedTable] at terminalFrame zeroSlots finalTable
  rw [indexedInverse] at finalInverse
  have indexedTime : 16 * incidences + 18 * formula.clauses.toList.length + 22 =
      16 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length + 18 * formula.clauses.toList.length + 22 := rfl
  have normalizedLive : normalized.liveWords ≤ normalizePeak := normalizeTrace.final_storage_le
  refine ⟨answer, queue, final, normalizeTicks + (16 * incidences + 18 * formula.clauses.toList.length + 22) + terminalTicks,
    max normalizePeak (max (normalized.liveWords + 2 * incidences + 1) terminalPeak),
    (by simpa only [Nat.add_assoc, incidences] using normalizeTrace.append (indexTrace.append terminalTrace)),
    ?_, ?_, finalSize, finalStack, ?_, finalPC, finalRunning, ?_, zeroSlots, decision, finalZero, finalTable, finalInverse, meaning, greatest⟩
  · dsimp only [incidences, count] at normalizeTime terminalTime ⊢
    cases answer <;> simp only [Bool.false_eq_true, ite_false, ite_true] at terminalTime ⊢ <;> omega
  · rw [indexedLive] at terminalSpace
    dsimp only [incidences] at normalizeSpace terminalSpace ⊢
    omega
  · simpa only [indexedOutput, normalizedOutput] using finalOutput
  · have tableBelow : layout.tableBase ≤ keep := by omega
    have sourceFrame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase state.heap indexed.heap :=
      ⟨by omega, by have := prefixFrame.2.1; omega,
        fun address below => prefixFrame.2.2 address (lt_of_lt_of_le below tableBelow)⟩
    exact Controller.Cost.ForestZeroBackendFrame.trans sourceFrame terminalFrame


/-- The query directory endpoint is an actual fetched operand. -/
theorem constructor_cursor_execution (program : Program width 8) (state : State width 8)
    (entry directoryEnd : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (capacity : entry + 1 < 2 ^ width)
    (present : program[entry]? = some (.constant 0 (word width directoryEnd))) :
    ∃ final, Execution program state final 1 state.liveWords ∧
      final.reg 0 = word width directoryEnd ∧ final.heap = state.heap ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 1) ∧ final.halted = false ∧
      (∀ register, register ≠ 0 → final.reg register = state.reg register) := by
  let final := state.advance.put 0 (word width directoryEnd)
  have actual : programStep program state = some final := by
    rw [fetched8 program state entry (.constant 0 (word width directoryEnd)) position (by omega) present]
    simp only [step, running, Bool.false_eq_true, ite_false]
    rfl
  have finalLive : final.liveWords = state.liveWords := rfl
  refine ⟨final, ?_, ?_, rfl, rfl, rfl, ?_, running, ?_⟩
  · simpa only [Nat.add_zero, finalLive, Nat.max_self] using Execution.cons actual (Execution.refl final)
  · simp only [final, State.put, Fin.reduceEq, ite_true]
  · have scalar : (word width entry).val = entry := Nat.mod_eq_of_lt (by omega)
    simp only [final, State.put, State.advance, position, scalar]
  · intro register different
    simp only [final, State.put, State.advance, ite_eq_right different]

/-- The source constructor executes inside the same eight-register caller. -/
theorem constructor_execution8 (program : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (represented : Represented heap layout dictionary) (channels sourceEnd : Nat)
    (references : List (List (Reference ambient)))
    (stored : ∀ reference ∈ references.flatten,
      Controller.Cost.ForestZeroEmit.StoredReference heap channels sourceEnd reference)
    (beforeTable : sourceEnd ≤ layout.tableBase) (beforeInverse : sourceEnd ≤ layout.inverseBase)
    (sourceBound : sourceEnd ≤ heap.size) (sourcePositive : 0 < sourceEnd)
    (channelCell : heap[0]? = some (word width channels)) (within : channels ≤ ambient)
    (entry returnPc : Nat) (stack output : List (Word width)) (saved : Fin 8 → Word width)
    (room : heap.size + 5 + 2 * (references.length + 1) +
      2 * references.flatten.length + 2 * ambient < 2 ^ width)
    (ambientFits : ambient + 1 < 2 ^ width)
    (capacity : entry + (constructorCode width entry heap.size heap.size (heap.size + 4) returnPc references).length < 2 ^ width)
    (present : ForestZeroCallerWiden.WidenedBlockAt program entry
      (constructorCode width entry heap.size heap.size (heap.size + 4) returnPc references)) :
    let refs := reservedReferences references
    let prepared := ForestZeroQueryCaller.queryHeap heap layout dictionary refs 0
    let emitted := ForestZeroQueryCaller.queryEmission heap layout dictionary refs 0
    let result := ForestZeroNonempty.search emitted.dictionary (emitted.dictionary.coordinates.size + 1) channels 0
    let covered := result.reason = .covered
    let slot := heap.size + 5 + 2 * references.length
    let installed := boundaryHeap
      (ForestZeroPositive.pairHeap prepared (ForestZeroPositive.channelLabels emitted.dictionary channels))
      slot prepared.size (prepared.size + 2 * channels)
    let finalHeap := if covered then
      activeHeap installed heap.size (heap.size + 4) (prepared.size + 2 * channels) (slot + 2)
      else activeHeap prepared heap.size (heap.size + 4) prepared.size slot
    let initial := Controller.Cost.RegisterWiden.widenState
      (atState heap entry (heap.size + 5 + 2 * (references.length + 1)) layout.tableBase
        dictionary.coordinates.size 0 (word width layout.inverseBase :: stack) output) saved
    let final := Controller.Cost.RegisterWiden.widenState
      (atState finalHeap returnPc (if covered then slot + 2 else slot)
        (if covered then prepared.size + 2 * channels else prepared.size)
        emitted.dictionary.coordinates.size 0 (word width layout.inverseBase :: stack) output) saved
    ∃ ticks peak, Execution program initial final ticks peak ∧
      ticks ≤ 79 + 5 * references.length + 23 * references.flatten.length +
        23 * emitted.dictionary.coordinates.size ∧
      peak ≤ 18 + heap.size + 2 * (references.length + 1) + 2 * references.flatten.length +
        2 * emitted.dictionary.coordinates.size + stack.length + output.length := by
  obtain ⟨ticks, peak, actual, timeBound, spaceBound⟩ :=
    constructor_execution (ForestZeroCallerWiden.lowerProgram program) heap layout dictionary
      represented channels sourceEnd references stored beforeTable beforeInverse sourceBound
      sourcePositive channelCell within entry returnPc stack output room ambientFits capacity
      (ForestZeroCallerWiden.lower_block program entry _ present)
  have widened := ForestZeroCallerWiden.execution program _ _ ticks peak actual rfl saved
  refine ⟨ticks, peak + 4, widened, timeBound, ?_⟩
  omega


/-- The dictionary and final query heap are computed by the source constructor. -/
abbrev constructorDictionary (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (references : List (List (Reference ambient))) : Dictionary ambient :=
  (compileRows dictionary (ForestZeroAssembly.originalRows (reservedReferences references))).1

def constructorHeap (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (references : List (List (Reference ambient))) (channels : Nat) :
    Array (Word width) :=
  let refs := reservedReferences references
  let prepared := ForestZeroQueryCaller.queryHeap heap layout dictionary refs 0
  let compiled := constructorDictionary heap layout dictionary references
  let result := ForestZeroNonempty.search compiled (compiled.coordinates.size + 1) channels 0
  let slot := heap.size + 5 + 2 * references.length
  if result.reason = .covered then
    activeHeap (boundaryHeap
      (ForestZeroPositive.pairHeap prepared (ForestZeroPositive.channelLabels compiled channels))
      slot prepared.size (prepared.size + 2 * channels))
      heap.size (heap.size + 4) (prepared.size + 2 * channels) (slot + 2)
  else activeHeap prepared heap.size (heap.size + 4) prepared.size slot

theorem constructorHeap_growth (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (references : List (List (Reference ambient))) (channels : Nat) :
    heap.size ≤ (constructorHeap heap layout dictionary references channels).size := by
  unfold constructorHeap
  dsimp only
  split_ifs <;> simp only [activeHeap_size, boundaryHeap_size, ForestZeroPositive.pairHeap_size,
    ForestZeroQueryCaller.queryHeap_size] <;> omega

def constructorDictionaryLayout (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (references : List (List (Reference ambient))) (channels : Nat) :
    Layout ambient (constructorHeap heap layout dictionary references channels).size where
  tableBase := layout.tableBase
  inverseBase := layout.inverseBase
  tableBound := Nat.le_trans layout.tableBound (constructorHeap_growth heap layout dictionary references channels)
  inverseBound := Nat.le_trans layout.inverseBound (constructorHeap_growth heap layout dictionary references channels)
  disjoint := layout.disjoint

/-- Optional nonemptiness stores affect query cells above the shared dictionary. -/
theorem constructor_dictionary_represented (heap : Array (Word width))
    (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (represented : Represented heap layout dictionary)
    (references : List (List (Reference ambient))) (channels : Nat) :
    Represented (constructorHeap heap layout dictionary references channels)
      (constructorDictionaryLayout heap layout dictionary references channels)
      (constructorDictionary heap layout dictionary references) := by
  let refs := reservedReferences references
  let prepared := ForestZeroQueryCaller.queryHeap heap layout dictionary refs 0
  let compiled := constructorDictionary heap layout dictionary references
  have preparedDictionary : Represented prepared (constructedLayout heap layout dictionary refs 0) compiled :=
    by simpa only [compiled, constructorDictionary, refs, ForestZeroQueryCaller.queryEmission_dictionary] using
      constructed_represented heap layout dictionary represented refs 0
  have preparedGrowth : heap.size ≤ prepared.size := by
    dsimp only [prepared]
    rw [ForestZeroQueryCaller.queryHeap_size]
    omega
  have frame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame heap.size prepared
      (constructorHeap heap layout dictionary references channels) := by
    refine ⟨preparedGrowth, constructorHeap_growth heap layout dictionary references channels, ?_⟩
    intro address below
    unfold constructorHeap
    dsimp only
    split_ifs
    · exact (active_prefix _ heap.size (heap.size + 4) _ _ address below (by omega)).trans
        ((boundary_prefix _ (heap.size + 5 + 2 * references.length) _ _ address (by omega)).trans
          (pairHeap_prefix prepared (ForestZeroPositive.channelLabels compiled channels) address
            (lt_of_lt_of_le below preparedGrowth)))
    · exact active_prefix prepared heap.size (heap.size + 4) _ _ address below (by omega)
  have actual := dictionary_prefix_transport prepared
    (constructorHeap heap layout dictionary references channels) heap.size
    (constructedLayout heap layout dictionary refs 0) compiled preparedDictionary frame
    (by change layout.tableBase + ambient ≤ heap.size; exact layout.tableBound)
    (by change layout.inverseBase + ambient ≤ heap.size; exact layout.inverseBound)
  exact actual



theorem constructor_covered_slots (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient)
    (covered : (ForestZeroNonempty.search
      (compileRows dictionary (ForestZeroAssembly.originalRows (reservedReferences references))).1
      ((compileRows dictionary (ForestZeroAssembly.originalRows (reservedReferences references))).1.coordinates.size + 1)
      channels 0).reason = .covered) :
    ∀ channel : Fin channels,
      (compileRows dictionary (ForestZeroAssembly.originalRows (reservedReferences references))).1.slots[
        (⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ : Fin ambient).val] ≠ 0 := by
  let compiled := (compileRows dictionary (ForestZeroAssembly.originalRows (reservedReferences references))).1
  have compiledCoherent : Coherent compiled :=
    (rows_dictionary dictionary coherent (ForestZeroAssembly.originalRows (reservedReferences references))).1
  have actual := ForestZeroNonempty.search_outcome compiled compiledCoherent channels within
  rcases actual with unused | allCovered
  · have impossible := unused.1
    rw [covered] at impossible
    cases impossible
  · exact allCovered.2.2

/-- The optional final clause is formed from the executed dictionary coverage test. -/
def constructorClauses (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient) :
    List (Clause (Fin (constructorDictionary heap layout dictionary references).coordinates.size)) :=
  let compiled := constructorDictionary heap layout dictionary references
  let original := originalClauses dictionary coherent references
  if covered : (ForestZeroNonempty.search compiled (compiled.coordinates.size + 1) channels 0).reason = .covered then
    original ++ [finiteClause (ForestZeroPositive.positiveClause compiled channels)
      (positiveClause_bounded compiled
        (rows_dictionary dictionary coherent (ForestZeroAssembly.originalRows (reservedReferences references))).1
        channels within (constructor_covered_slots dictionary coherent references channels within covered))]
  else original

/-- The complete source is the original rows and precisely the installed optional row. -/
theorem constructor_clauses_stored (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (represented : Represented heap layout dictionary)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient) :
    Stored (constructorClauses heap layout dictionary represented.coherent references channels within)
      (heap.size + 5) (heap.size + 5 + 2 * (references.length + 1))
      (constructorHeap heap layout dictionary references channels) := by
  let refs := reservedReferences references
  let prepared := ForestZeroQueryCaller.queryHeap heap layout dictionary refs 0
  let compiled := constructorDictionary heap layout dictionary references
  let original := originalClauses dictionary represented.coherent references
  let source := heap.size + 5 + 2 * (references.length + 1)
  let slot := heap.size + 5 + 2 * references.length
  have originalStored : Stored original (heap.size + 5) source prepared :=
    reserved_query_stored heap layout dictionary represented references 0
  have originalEnd : sourceOffset original source original.length = prepared.size :=
    originalClauses_end heap layout dictionary represented.coherent references 0
  have originalLength : original.length = references.length :=
    originalClauses_length dictionary represented.coherent references
  have preparedSize : prepared.size = heap.size + 5 + 2 * (references.length + 1) +
      2 * references.flatten.length := by
    simp only [prepared, refs, ForestZeroQueryCaller.queryHeap_size,
      reservedReferences_length, reservedReferences_flatten]
  by_cases covered : (ForestZeroNonempty.search compiled (compiled.coordinates.size + 1) channels 0).reason = .covered
  · let bounds := positiveClause_bounded compiled
      (rows_dictionary dictionary represented.coherent (ForestZeroAssembly.originalRows refs)).1
      channels within (constructor_covered_slots dictionary represented.coherent references channels within covered)
    let last := finiteClause (ForestZeroPositive.positiveClause compiled channels) bounds
    have raw : last.map (fun literal => (literal.1.val, literal.2)) =
        (ForestZeroPositive.channelLabels compiled channels).map (fun label => (label, true)) :=
      ForestZeroAssembly.finiteClause_raw _ bounds
    have installed := installed_positive_active original last
      (ForestZeroPositive.channelLabels compiled channels) prepared (heap.size + 5) source
      heap.size (heap.size + 4) originalStored originalEnd
      (by dsimp only [source]; rw [originalLength]; omega)
      (by rw [originalLength]; omega) (by omega) (by omega) (by omega) (by omega) raw
    simpa only [constructorClauses, constructorHeap, compiled, refs, dite_eq_left covered, ite_eq_left covered,
      original, last, bounds, prepared, source,
      ForestZeroPositive.pairHeap_size, ForestZeroPositive.channelLabels_length,
      originalLength, slot, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using installed
  · have retained := stored_active originalStored heap.size (heap.size + 4) prepared.size slot
      (by rw [preparedSize]; omega) (by rw [preparedSize]; omega) (by omega) (by omega)
      (by dsimp only [source]; omega)
    simpa only [constructorClauses, constructorHeap, compiled, refs, dite_eq_right covered, ite_eq_right covered,
      original, prepared, source, slot] using retained

theorem constructorClauses_length (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient) :
    (constructorClauses heap layout dictionary coherent references channels within).length =
      references.length +
        (if (ForestZeroNonempty.search (constructorDictionary heap layout dictionary references)
          ((constructorDictionary heap layout dictionary references).coordinates.size + 1) channels 0).reason = .covered
          then 1 else 0) := by
  unfold constructorClauses
  dsimp only
  split_ifs <;> simp only [List.length_append, List.length_cons, List.length_nil,
    originalClauses_length] <;> omega

theorem constructorClauses_profile_bound (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient) :
    ((constructorClauses heap layout dictionary coherent references channels within).map List.length).sum ≤
      references.flatten.length + (constructorDictionary heap layout dictionary references).coordinates.size := by
  let compiled := constructorDictionary heap layout dictionary references
  have compiledCoherent : Coherent compiled :=
    (rows_dictionary dictionary coherent (ForestZeroAssembly.originalRows (reservedReferences references))).1
  unfold constructorClauses
  dsimp only
  split_ifs with covered
  · have slots := constructor_covered_slots dictionary coherent references channels within covered
    have channelBound := ForestZeroPositive.covered_count compiled compiledCoherent channels within slots
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero, finiteClause, List.length_map,
      List.length_attach, ForestZeroPositive.positiveClause, ForestZeroPositive.channelLabels_length,
      originalClauses_profile, List.length_flatten]
    exact Nat.add_le_add_left channelBound _
  · simp only [originalClauses_profile, List.length_flatten]
    omega

/-- Fin conversion and the optional all-positive clause preserve the source grammar. -/
theorem constructorClauses_dualHorn (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient)
    (sourceDual : Controller.Horn.DualHorn
      (ofClauses (ForestZeroAssembly.originalRows (reservedReferences references)))) :
    Controller.Horn.DualHorn (ofClauses (constructorClauses heap layout dictionary coherent references channels within)) := by
  have all := Controller.Cost.ForestZeroGrammar.compiled_finite_dualHorn dictionary coherent
    (ForestZeroAssembly.originalRows (reservedReferences references)) sourceDual
  have originalDual : ∀ clause ∈ originalClauses dictionary coherent references,
      Controller.Horn.DualHornClause clause := by
    intro clause member
    apply all
    change clause ∈ (reservedClauses dictionary coherent references).take references.length at member
    have fullMember := List.mem_of_mem_take member
    simpa only [originalClauses, reservedClauses, ForestZeroAssembly.finiteClauses,
      finiteRows, ofClauses, List.mem_toArray] using fullMember
  intro clause member
  simp only [ofClauses, List.mem_toArray] at member
  unfold constructorClauses at member
  dsimp only at member
  split_ifs at member
  · rcases List.mem_append.mp member with old | last
    · exact originalDual clause old
    · have equality : clause = _ := List.mem_singleton.mp last
      subst clause
      apply Controller.Cost.ForestZeroGrammar.finiteClause_dualHorn
      right
      intro left leftMember right rightMember leftNegative rightNegative
      change left ∈ (ForestZeroPositive.channelLabels _ channels).map (fun label => (label, true)) at leftMember
      obtain ⟨label, _, same⟩ := List.mem_map.mp leftMember
      have impossible : true = false := (congrArg Prod.snd same).trans leftNegative
      cases impossible
  · exact originalDual clause member

theorem constructorHeap_size (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (references : List (List (Reference ambient))) (channels : Nat) :
    (constructorHeap heap layout dictionary references channels).size =
      heap.size + 5 + 2 * (references.length + 1) + 2 * references.flatten.length +
        (if (ForestZeroNonempty.search (constructorDictionary heap layout dictionary references)
          ((constructorDictionary heap layout dictionary references).coordinates.size + 1) channels 0).reason = .covered
          then 2 * channels else 0) := by
  unfold constructorHeap
  dsimp only
  split_ifs <;> simp only [activeHeap_size, boundaryHeap_size, ForestZeroPositive.pairHeap_size,
    ForestZeroPositive.channelLabels_length, ForestZeroQueryCaller.queryHeap_size,
    reservedReferences_length, reservedReferences_flatten] <;> omega

theorem constructorClauses_literal_count (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient) :
    ((constructorClauses heap layout dictionary coherent references channels within).map List.length).sum =
      references.flatten.length +
        (if (ForestZeroNonempty.search (constructorDictionary heap layout dictionary references)
          ((constructorDictionary heap layout dictionary references).coordinates.size + 1) channels 0).reason = .covered
          then channels else 0) := by
  unfold constructorClauses
  dsimp only
  split_ifs <;> simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, finiteClause, List.length_map,
    List.length_attach, ForestZeroPositive.positiveClause, ForestZeroPositive.channelLabels_length,
    originalClauses_profile, List.length_flatten] <;> omega

theorem constructorClauses_source_end (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient) :
    sourceOffset (constructorClauses heap layout dictionary coherent references channels within)
      (heap.size + 5 + 2 * (references.length + 1))
      (constructorClauses heap layout dictionary coherent references channels within).length =
      (constructorHeap heap layout dictionary references channels).size := by
  unfold sourceOffset
  rw [List.take_length, constructorClauses_literal_count, constructorHeap_size]
  split_ifs <;> omega

/-- The source layout is formed from the same emitted headers and source end. -/
def constructorBackend (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient) :
    Controller.Horn.SourceDirectory.Layout
      (constructorClauses heap layout dictionary coherent references channels within) :=
  backendLayout (constructorClauses heap layout dictionary coherent references channels within)
    heap.size (heap.size + 5 + 2 * (references.length + 1))
    (constructorHeap heap layout dictionary references channels).size
    (by rw [constructorClauses_length]; split_ifs <;> omega)
    (constructorClauses_source_end heap layout dictionary coherent references channels within).le

theorem constructor_canonical_inputs (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (represented : Represented heap layout dictionary)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient) :
    let clauses := constructorClauses heap layout dictionary represented.coherent references channels within
    let backend := constructorBackend heap layout dictionary represented.coherent references channels within
    let finalHeap := constructorHeap heap layout dictionary references channels
    Stored clauses backend.directory backend.source finalHeap ∧
      CursorStored backend.directory backend.directoryHeader finalHeap ∧
      CursorStored (backend.directory + 2 * clauses.length) backend.endHeader finalHeap := by
  refine ⟨constructor_clauses_stored heap layout dictionary represented references channels within, ?_, ?_⟩
  · apply cursorStored_of_option (by change heap.size + 3 < _; rw [constructorHeap_size]; split_ifs <;> omega)
    exact (constructor_header_cells heap layout dictionary represented references channels 0).1
  · apply cursorStored_of_option (by change heap.size + 4 < _; rw [constructorHeap_size]; split_ifs <;> omega)
    have cell := (constructor_header_cells heap layout dictionary represented references channels 0).2
    change (constructorHeap heap layout dictionary references channels)[heap.size + 4]? =
      some (word width (heap.size + 5 + 2 *
        (constructorClauses heap layout dictionary represented.coherent references channels within).length))
    rw [constructorClauses_length]
    have endEq : heap.size + 5 + 2 * (if (ForestZeroNonempty.search (constructorDictionary heap layout dictionary references)
        ((constructorDictionary heap layout dictionary references).coordinates.size + 1) channels 0).reason = .covered
        then references.length + 1 else references.length) =
        heap.size + 5 + 2 * (references.length +
          (if (ForestZeroNonempty.search (constructorDictionary heap layout dictionary references)
            ((constructorDictionary heap layout dictionary references).coordinates.size + 1) channels 0).reason = .covered then 1 else 0)) := by
      split_ifs <;> omega
    exact cell.trans (congrArg (fun value => some (word width value)) endEq)

/-- No local coordinate is created without an original literal occurrence. -/
theorem constructorDictionary_size_bound (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (references : List (List (Reference ambient))) :
    (constructorDictionary heap layout dictionary references).coordinates.size ≤
      dictionary.coordinates.size + references.flatten.length := by
  have actual := (rows_local_size dictionary
    (ForestZeroAssembly.originalRows (reservedReferences references))).2
  simpa only [constructorDictionary, literalCount, ForestZeroAssembly.originalRows,
    List.map_map, Function.comp_def, List.length_map, ← List.length_flatten,
    reservedReferences_flatten] using actual


def constructorState (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (references : List (List (Reference ambient)))
    (channels entry : Nat) (stack output : List (Word width)) (saved : Fin 8 → Word width) : State width 8 :=
  let compiled := constructorDictionary heap layout dictionary references
  let result := ForestZeroNonempty.search compiled (compiled.coordinates.size + 1) channels 0
  let slot := heap.size + 5 + 2 * references.length
  Controller.Cost.RegisterWiden.widenState
    (atState (constructorHeap heap layout dictionary references channels) entry
      (if result.reason = .covered then slot + 2 else slot)
      (constructorHeap heap layout dictionary references channels).size
      compiled.coordinates.size 0 (word width layout.inverseBase :: stack) output) saved

/-- Widening retains exactly the source constructor's executed endpoint. -/
theorem constructor_state_execution (program : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (represented : Represented heap layout dictionary) (channels sourceEnd : Nat)
    (references : List (List (Reference ambient)))
    (stored : ∀ reference ∈ references.flatten,
      Controller.Cost.ForestZeroEmit.StoredReference heap channels sourceEnd reference)
    (beforeTable : sourceEnd ≤ layout.tableBase) (beforeInverse : sourceEnd ≤ layout.inverseBase)
    (sourceBound : sourceEnd ≤ heap.size) (sourcePositive : 0 < sourceEnd)
    (channelCell : heap[0]? = some (word width channels)) (within : channels ≤ ambient)
    (entry returnPc : Nat) (stack output : List (Word width)) (saved : Fin 8 → Word width)
    (room : heap.size + 5 + 2 * (references.length + 1) +
      2 * references.flatten.length + 2 * ambient < 2 ^ width)
    (ambientFits : ambient + 1 < 2 ^ width)
    (capacity : entry + (constructorCode width entry heap.size heap.size (heap.size + 4) returnPc references).length < 2 ^ width)
    (present : ForestZeroCallerWiden.WidenedBlockAt program entry
      (constructorCode width entry heap.size heap.size (heap.size + 4) returnPc references)) :
    ∃ ticks peak, Execution program
      (Controller.Cost.RegisterWiden.widenState
        (atState heap entry (heap.size + 5 + 2 * (references.length + 1)) layout.tableBase
          dictionary.coordinates.size 0 (word width layout.inverseBase :: stack) output) saved)
      (constructorState heap layout dictionary references channels returnPc stack output saved) ticks peak ∧
      ticks ≤ 79 + 5 * references.length + 23 * references.flatten.length +
        23 * (constructorDictionary heap layout dictionary references).coordinates.size ∧
      peak ≤ 18 + heap.size + 2 * (references.length + 1) + 2 * references.flatten.length +
        2 * (constructorDictionary heap layout dictionary references).coordinates.size + stack.length + output.length := by
  obtain ⟨ticks, peak, actual, timeBound, spaceBound⟩ := constructor_execution8 program heap
    layout dictionary represented channels sourceEnd references stored beforeTable beforeInverse
    sourceBound sourcePositive channelCell within entry returnPc stack output saved room ambientFits capacity present
  have endScalar :
      (if (ForestZeroNonempty.search (constructorDictionary heap layout dictionary references)
        ((constructorDictionary heap layout dictionary references).coordinates.size + 1) channels 0).reason = .covered
          then (ForestZeroQueryCaller.queryHeap heap layout dictionary (reservedReferences references) 0).size + 2 * channels
          else (ForestZeroQueryCaller.queryHeap heap layout dictionary (reservedReferences references) 0).size) =
      (constructorHeap heap layout dictionary references channels).size := by
    unfold constructorHeap
    dsimp only
    split_ifs <;> simp only [activeHeap_size, boundaryHeap_size, ForestZeroPositive.pairHeap_size,
      ForestZeroPositive.channelLabels_length]
  simp only [ForestZeroQueryCaller.queryEmission_dictionary] at actual timeBound spaceBound
  simp only [constructorDictionary] at endScalar
  rw [endScalar] at actual
  refine ⟨ticks, peak, ?_, ?_, ?_⟩
  · simpa only [constructorState, constructorDictionary, constructorHeap] using actual
  · simpa only [constructorDictionary, ForestZeroQueryCaller.queryEmission_dictionary] using timeBound
  · simpa only [constructorDictionary, ForestZeroQueryCaller.queryEmission_dictionary] using spaceBound


/-- Original source cells survive both optional-row outcomes. -/
theorem constructor_source_cell (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (references : List (List (Reference ambient)))
    (channels sourceEnd address : Nat) (beforeTable : sourceEnd ≤ layout.tableBase)
    (beforeInverse : sourceEnd ≤ layout.inverseBase) (sourceBound : sourceEnd ≤ heap.size)
    (valid : address < sourceEnd) :
    (constructorHeap heap layout dictionary references channels)[address]? = heap[address]? := by
  let prepared := ForestZeroQueryCaller.queryHeap heap layout dictionary (reservedReferences references) 0
  let compiled := constructorDictionary heap layout dictionary references
  have old : address < heap.size := lt_of_lt_of_le valid sourceBound
  have growth : heap.size ≤ prepared.size := by
    dsimp only [prepared]
    rw [ForestZeroQueryCaller.queryHeap_size]
    omega
  have original := query_original_cell heap layout dictionary (reservedReferences references)
    0 sourceEnd address beforeTable beforeInverse valid sourceBound
  unfold constructorHeap
  dsimp only
  split_ifs
  · exact (active_prefix _ heap.size (heap.size + 4) _ _ address old (by omega)).trans
      ((boundary_prefix _ (heap.size + 5 + 2 * references.length) _ _ address (by omega)).trans
        ((pairHeap_prefix prepared (ForestZeroPositive.channelLabels compiled channels) address
          (lt_of_lt_of_le old growth)).trans original))
  · exact (active_prefix prepared heap.size (heap.size + 4) _ _ address old (by omega)).trans original

/-- Every source reference still names the same loaded cell after a protected
prefix trace; repeated references remain repeated occurrences. -/
theorem stored_reference_prefix {before after : Array (Word width)} {channels sourceEnd : Nat}
    {reference : Reference ambient}
    (stored : ForestZeroEmit.StoredReference before channels sourceEnd reference)
    (frame : ForestZeroBackendFrame.PrefixFrame sourceEnd before after) :
    ForestZeroEmit.StoredReference after channels sourceEnd reference := by
  refine ⟨frame.2.1, stored.slotBound, stored.headerBound, ?_, ?_, stored.coordinateEq⟩
  · exact (frame.2.2 reference.slot stored.slotBound).trans stored.slotWord
  · exact (frame.2.2 0 stored.headerBound).trans stored.channelWord

/-- Reset table cells represent a reusable empty dictionary. Inverse cells do
not require clearing because the empty dictionary has no allocated indices. -/
theorem empty_dictionary_from_zero_table (heap : Array (Word width))
    (layout : Layout ambient heap.size)
    (zeroTable : ∀ coordinate : Fin ambient,
      heap[layout.tableBase + coordinate.val]? = some (word width 0)) :
    Represented heap layout (ForestZeroCompile.empty ambient) := by
  refine ⟨ForestZeroCompile.empty_coherent ambient, ?_, ?_⟩
  · intro coordinate
    simpa [ForestZeroCompile.empty] using zeroTable coordinate
  · intro index coordinate allocated
    simp only [ForestZeroCompile.empty, Array.getElem?_empty] at allocated
    cases allocated

/-- Source construction preserves every cell below the dictionary, including
loaded headers and each original occurrence cell used by another query. -/
theorem constructor_prefix (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (references : List (List (Reference ambient)))
    (channels : Nat) (adjacent : layout.inverseBase = layout.tableBase + ambient) :
    ForestZeroBackendFrame.PrefixFrame layout.tableBase heap
      (constructorHeap heap layout dictionary references channels) := by
  have old : layout.tableBase ≤ heap.size := by have := layout.tableBound; omega
  refine ⟨old, Nat.le_trans old (constructorHeap_growth heap layout dictionary references channels), ?_⟩
  intro address below
  exact constructor_source_cell heap layout dictionary references channels layout.tableBase address
    (le_refl _) (by omega) old below


/-- Formula conversion retains every emitted clause and its order. -/
def constructorFormula (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient) :=
  ofClauses (constructorClauses heap layout dictionary coherent references channels within)

theorem constructorFormula_rows (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient) :
    (constructorFormula heap layout dictionary coherent references channels within).clauses.toList =
      constructorClauses heap layout dictionary coherent references channels within := by
  simp only [constructorFormula, ofClauses, List.toList_toArray]

def constructorFormulaBackend (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient) :
    Controller.Horn.SourceDirectory.Layout
      (constructorFormula heap layout dictionary coherent references channels within).clauses.toList :=
  backendLayout (constructorFormula heap layout dictionary coherent references channels within).clauses.toList
    heap.size (heap.size + 5 + 2 * (references.length + 1))
    (constructorHeap heap layout dictionary references channels).size
    (by rw [constructorFormula_rows, constructorClauses_length]; split_ifs <;> omega)
    (by rw [constructorFormula_rows]; exact
      (constructorClauses_source_end heap layout dictionary coherent references channels within).le)


/-- The failed-query register ABI is converted to the constructor stack by
three fetched instructions; no saved inverse word is supplied externally. -/
def reuseEntryCode (width : Nat) : Array (Instruction width 8) :=
  #[.push 2, .constant 2 (word width 0), .constant 3 (word width 0)]

theorem reuse_entry_execution (program : Program width 8) (heap : Array (Word width))
    (entry table inverse scratch : Nat) (rest output : List (Word width)) (saved : Fin 8 → Word width)
    (fits : entry + 3 < 2 ^ width)
    (present : ∀ phase : Fin 3, program[entry + phase.val]? = (reuseEntryCode width)[phase.val]?) :
    Execution program
      (RegisterWiden.widenState (atState heap entry 0 table inverse scratch rest output) saved)
      (RegisterWiden.widenState (atState heap (entry + 3) 0 table 0 0
        (word width inverse :: rest) output) saved)
      3 (10 + heap.size + rest.length + output.length) := by
  let s0 := RegisterWiden.widenState (atState heap entry 0 table inverse scratch rest output) saved
  let s1 := RegisterWiden.widenState (atState heap (entry + 1) 0 table inverse scratch (word width inverse :: rest) output) saved
  let s2 := RegisterWiden.widenState (atState heap (entry + 2) 0 table 0 scratch (word width inverse :: rest) output) saved
  let s3 := RegisterWiden.widenState (atState heap (entry + 3) 0 table 0 0 (word width inverse :: rest) output) saved
  have first : programStep program s0 = some s1 := by
    rw [fetched8 program s0 entry (.push 2) rfl (by omega)
      (by simpa [reuseEntryCode, Nat.add_zero] using present ⟨0, by decide⟩)]
    change some { s0.advance with stack := s0.reg 2 :: s0.stack } = some s1
    have value : s0.reg 2 = word width inverse := rfl
    rw [value]
    change some (RegisterWiden.widenState
      { (atState heap entry 0 table inverse scratch rest output).advance with
          stack := word width inverse :: rest } saved) = some s1
    rw [advance_at _ _ _ _ _ _ _ _ (by omega)]
    rfl
  have second : programStep program s1 = some s2 := by
    rw [fetched8 program s1 (entry + 1) (.constant 2 (word width 0)) rfl (by omega)
      (by simpa [reuseEntryCode] using present ⟨1, by decide⟩)]
    change some (s1.advance.put 2 (word width 0)) = some s2
    have advanced := advance_at heap (entry + 1) 0 table inverse scratch (word width inverse :: rest) output (by omega)
    dsimp only [s1, s2]
    rw [RegisterWiden.widenState_advance, advanced]
    have put := RegisterWiden.widenState_put
      (atState heap (entry + 1 + 1) 0 table inverse scratch (word width inverse :: rest) output)
      saved (2 : Fin 4) (word width 0)
    change (RegisterWiden.widenState
      (atState heap (entry + 1 + 1) 0 table inverse scratch (word width inverse :: rest) output) saved).put
      (2 : Fin 8) (word width 0) = _ at put
    rw [put, put2_at]

  have third : programStep program s2 = some s3 := by
    rw [fetched8 program s2 (entry + 2) (.constant 3 (word width 0)) rfl (by omega)
      (by simpa [reuseEntryCode] using present ⟨2, by decide⟩)]
    change some (s2.advance.put 3 (word width 0)) = some s3
    have advanced := advance_at heap (entry + 2) 0 table 0 scratch (word width inverse :: rest) output (by omega)
    dsimp only [s2, s3]
    rw [RegisterWiden.widenState_advance, advanced]
    have put := RegisterWiden.widenState_put
      (atState heap (entry + 2 + 1) 0 table 0 scratch (word width inverse :: rest) output)
      saved (3 : Fin 4) (word width 0)
    change (RegisterWiden.widenState
      (atState heap (entry + 2 + 1) 0 table 0 scratch (word width inverse :: rest) output) saved).put
      (3 : Fin 8) (word width 0) = _ at put
    rw [put, put3_at]

  convert Execution.cons first (Execution.cons second (Execution.cons third (Execution.refl s3))) using 1 <;>
    simp only [s0, s1, s2, s3, RegisterWiden.widenState, State.liveWords,
      atState, List.length_cons, Nat.max_self, ite_self] <;> omega

/-- The keep endpoint is read from both physical headers and the retained
inverse base; a fetched constant then names this query's actual directory end. -/
theorem keep_cursor_execution8 (program : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (channels nodes entry : Nat)
    (references : List (List (Reference ambient))) (rest output : List (Word width))
    (saved : Fin 8 → Word width) (ambientEq : ambient = channels + nodes)
    (endpoint : heap.size = layout.inverseBase + ambient)
    (headerRoom : 1 < heap.size) (channelsCell : heap[0]? = some (word width channels))
    (nodesCell : heap[1]? = some (word width nodes)) (room : heap.size < 2 ^ width)
    (fits : entry + 12 < 2 ^ width)
    (keepAt : ForestZeroCallerWiden.WidenedBlockAt program entry (keepCode width))
    (cursorAt : program[entry + 11]? = some (.constant 0
      (word width (heap.size + 5 + 2 * (references.length + 1))))) :
    Execution program
      (RegisterWiden.widenState (atState heap entry 0 layout.tableBase 0 0
        (word width layout.inverseBase :: rest) output) saved)
      (RegisterWiden.widenState (atState heap (entry + 12)
        (heap.size + 5 + 2 * (references.length + 1)) layout.tableBase 0 0
        (word width layout.inverseBase :: word width heap.size :: rest) output) saved)
      12 (11 + heap.size + rest.length + output.length) := by
  have low := keep_execution (ForestZeroCallerWiden.lowerProgram program) heap entry
    layout.tableBase layout.inverseBase channels nodes rest output headerRoom channelsCell nodesCell
    (by omega) (by omega) (by omega) (ForestZeroCallerWiden.lower_block program entry _ keepAt)
  have kept := ForestZeroCallerWiden.execution program _ _ _ _ low rfl saved
  have keepEq : layout.inverseBase + (channels + nodes) = heap.size := by omega
  rw [keepEq] at kept
  let middle := RegisterWiden.widenState (atState heap (entry + 11) heap.size layout.tableBase 0 0
    (word width layout.inverseBase :: word width heap.size :: rest) output) saved
  let final := middle.advance.put 0 (word width (heap.size + 5 + 2 * (references.length + 1)))
  have transition : programStep program middle = some final := by
    rw [fetched8 program middle (entry + 11)
      (.constant 0 (word width (heap.size + 5 + 2 * (references.length + 1)))) rfl (by omega) cursorAt]
    rfl
  have finalEq : final = RegisterWiden.widenState (atState heap (entry + 12)
      (heap.size + 5 + 2 * (references.length + 1)) layout.tableBase 0 0
      (word width layout.inverseBase :: word width heap.size :: rest) output) saved := by
    dsimp only [final, middle]
    rw [RegisterWiden.widenState_advance]
    have put := RegisterWiden.widenState_put
      (atState heap (entry + 11) heap.size layout.tableBase 0 0
        (word width layout.inverseBase :: word width heap.size :: rest) output).advance
      saved (0 : Fin 4) (word width (heap.size + 5 + 2 * (references.length + 1)))
    change (RegisterWiden.widenState
      (atState heap (entry + 11) heap.size layout.tableBase 0 0
        (word width layout.inverseBase :: word width heap.size :: rest) output).advance saved).put
      (0 : Fin 8) (word width (heap.size + 5 + 2 * (references.length + 1))) = _ at put
    rw [put, advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]

  have last : Execution program middle final 1 (11 + heap.size + rest.length + output.length) := by
    convert Execution.cons transition (Execution.refl final) using 1 <;>
      simp only [middle, final, State.put, State.advance, State.liveWords,
        RegisterWiden.widenState, atState, List.length_cons] <;> omega
  rw [finalEq] at last
  convert kept.append last using 1 <;> (try simp only [Nat.add_assoc]) <;> omega


/-- Failed queries resume at their next occurrence's stored entry with the
same loaded source, empty allocator table, and restored low-register ABI. -/
structure QueryReady {ambient : Nat} (sourceHeap : Array (Word width)) (tableBase inverseBase entry : Nat)
    (rest : List (Word width)) (state : State width 8) : Prop where
  heapSize : state.heap.size = sourceHeap.size
  sourceFrame : ForestZeroBackendFrame.PrefixFrame tableBase sourceHeap state.heap
  zeroTable : ∀ coordinate : Fin ambient,
    state.heap[tableBase + coordinate.val]? = some (word width 0)
  stack : state.stack = rest
  position : state.pc = word width entry
  running : state.halted = false
  zeroRegister : state.reg 0 = word width 0
  tableRegister : state.reg 1 = word width tableBase
  inverseRegister : state.reg 2 = word width inverseBase

/-- Readiness identifies the complete eight-register query entry from actual
register values. High registers and the unconstrained scratch register are
retained; no precomputed source operands are introduced. -/
theorem QueryReady.entry_state
    {sourceHeap : Array (Word width)} {tableBase inverseBase entry : Nat}
    {rest : List (Word width)} {state : State width 8}
    (ready : QueryReady (ambient := ambient) sourceHeap tableBase inverseBase entry rest state) :
    RegisterWiden.widenState
      (atState state.heap entry 0 tableBase inverseBase (state.reg 3).val rest state.output)
      state.reg = state := by
  have scratch : word width (state.reg 3).val = state.reg 3 := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt (state.reg 3).isLt
  have registers : (RegisterWiden.widenState
      (atState state.heap entry 0 tableBase inverseBase (state.reg 3).val rest state.output)
      state.reg).reg = state.reg := by
    funext register
    fin_cases register
    · simpa [RegisterWiden.widenState, atState] using ready.zeroRegister.symm
    · simpa [RegisterWiden.widenState, atState] using ready.tableRegister.symm
    · simpa [RegisterWiden.widenState, atState] using ready.inverseRegister.symm
    · simpa [RegisterWiden.widenState, atState] using scratch
    all_goals rfl
  change State.mk _ state.heap rest state.output (word width entry) false =
    State.mk state.reg state.heap state.stack state.output state.pc state.halted
  rw [State.mk.injEq]
  exact ⟨registers, rfl, ready.stack.symm, rfl, ready.position.symm, ready.running.symm⟩

/-- The actual reset endpoint supplies an empty represented dictionary for
another occurrence. Allocated inverse cells are not scanned or cleared. -/
theorem QueryReady.empty_representation
    {sourceHeap : Array (Word width)} {tableBase inverseBase entry : Nat}
    {rest : List (Word width)} {state : State width 8}
    (ready : QueryReady (ambient := ambient) sourceHeap tableBase inverseBase entry rest state)
    (layout : Layout ambient sourceHeap.size)
    (tableEq : layout.tableBase = tableBase) (inverseEq : layout.inverseBase = inverseBase) :
    ∃ actualLayout : Layout ambient state.heap.size,
      actualLayout.tableBase = tableBase ∧ actualLayout.inverseBase = inverseBase ∧
      Represented state.heap actualLayout (ForestZeroCompile.empty ambient) := by
  let actualLayout : Layout ambient state.heap.size :=
    { tableBase := tableBase
      inverseBase := inverseBase
      tableBound := by rw [ready.heapSize, ← tableEq]; exact layout.tableBound
      inverseBound := by rw [ready.heapSize, ← inverseEq]; exact layout.inverseBound
      disjoint := by simpa only [tableEq, inverseEq] using layout.disjoint }
  exact ⟨actualLayout, rfl, rfl, empty_dictionary_from_zero_table state.heap actualLayout ready.zeroTable⟩

/-- Each reference for a later occurrence continues to name its original
stored cell; this applies separately to duplicate occurrences. -/
theorem QueryReady.stored_reference
    {sourceHeap : Array (Word width)} {tableBase inverseBase entry : Nat}
    {rest : List (Word width)} {state : State width 8}
    (ready : QueryReady (ambient := ambient) sourceHeap tableBase inverseBase entry rest state)
    {channels sourceEnd : Nat} (sourceBeforeTable : sourceEnd ≤ tableBase)
    {reference : Reference ambient}
    (stored : ForestZeroEmit.StoredReference sourceHeap channels sourceEnd reference) :
    ForestZeroEmit.StoredReference state.heap channels sourceEnd reference := by
  have restricted : ForestZeroBackendFrame.PrefixFrame sourceEnd sourceHeap state.heap :=
    ⟨Nat.le_trans sourceBeforeTable ready.sourceFrame.1,
      Nat.le_trans sourceBeforeTable ready.sourceFrame.2.1,
      fun address below => ready.sourceFrame.2.2 address (lt_of_lt_of_le below sourceBeforeTable)⟩
  exact stored_reference_prefix stored restricted

/-- Physical branch-zero dispatch changes only PC and running status. The
source/reset fields returned by the full query trace therefore establish
readiness at the next occurrence's actual code address. -/
theorem failed_query_dispatch_ready
    (sourceHeap : Array (Word width)) (tableBase inverseBase dispatchEntry next : Nat)
    (rest : List (Word width)) (final : State width 8)
    (heapSize : final.heap.size = sourceHeap.size)
    (sourceFrame : ForestZeroBackendFrame.PrefixFrame tableBase sourceHeap final.heap)
    (zeroTable : ∀ coordinate : Fin ambient,
      final.heap[tableBase + coordinate.val]? = some (word width 0))
    (stack : final.stack = rest)
    (zeroRegister : final.reg 0 = word width 0)
    (tableRegister : final.reg 1 = word width tableBase)
    (inverseRegister : final.reg 2 = word width inverseBase) :
    QueryReady (ambient := ambient) sourceHeap tableBase inverseBase next rest
      (ForestZeroRootLoop.dispatchState final dispatchEntry next false) := by
  exact ⟨heapSize, sourceFrame, zeroTable, stack, rfl, rfl,
    zeroRegister, tableRegister, inverseRegister⟩


/-- One query executes its actual source constructor and then the complete
normalization, indexed decision, original-channel projection and touched reset.
The clause list, directory and represented dictionary are derived from that
constructor; the fixed program supplies only the fetched instruction blocks. -/
theorem source_constructor_original_reuse_execution {channels ambient : Nat}
    (heap : Array (Word width)) (originalLayout : Layout ambient heap.size)
    (originalDictionary : Dictionary ambient) (originalRepresentation : Represented heap originalLayout originalDictionary)
    (references : List (List (Reference ambient))) (sourceEnd nodes : Nat)
    (sourceReferences : ∀ reference ∈ references.flatten,
      Controller.Cost.ForestZeroEmit.StoredReference heap channels sourceEnd reference)
    (sourceBeforeTable : sourceEnd ≤ originalLayout.tableBase)
    (sourceBeforeInverse : sourceEnd ≤ originalLayout.inverseBase)
    (sourceBound : sourceEnd ≤ heap.size) (sourcePositive : 0 < sourceEnd)
    (sourceChannel : heap[0]? = some (word width channels))
    (sourceNodes : heap[1]? = some (word width nodes)) (ambientEq : ambient = channels + nodes)
    (adjacent : originalLayout.inverseBase = originalLayout.tableBase + ambient)
    (tablePositive : 0 < originalLayout.tableBase) (sourceHeaderRoom : 1 < sourceEnd)
    (sourceDual : Controller.Horn.DualHorn
      (ofClauses (ForestZeroAssembly.originalRows (reservedReferences references))))
    (program : Program width 8) (sourceEntry constructorEntry entry : Nat)
    (entryEq : constructorEntry = sourceEntry + 15)
    (originalCount : originalDictionary.coordinates.size = 0)
    (sourceEndpoint : heap.size = originalLayout.inverseBase + ambient)
    (initialScratch : Nat)
    (entryCapacity : sourceEntry + 15 < 2 ^ width)
    (entryAt : ∀ phase : Fin 3, program[sourceEntry + phase.val]? = (reuseEntryCode width)[phase.val]?)
    (keepAt : ForestZeroCallerWiden.WidenedBlockAt program (sourceEntry + 3) (keepCode width))
    (cursorAt : program[sourceEntry + 14]? = some (.constant 0
      (word width (heap.size + 5 + 2 * (references.length + 1)))))
    (rest output : List (Word width)) (highRegisters : Fin 8 → Word width)
    (constructorRoom : heap.size + 5 + 2 * (references.length + 1) +
      2 * references.flatten.length + 2 * ambient < 2 ^ width)
    (ambientFits : ambient + 1 < 2 ^ width)
    (constructorCapacity : constructorEntry +
      (constructorCode width constructorEntry heap.size heap.size (heap.size + 4) entry references).length < 2 ^ width)
    (constructorAt : ForestZeroCallerWiden.WidenedBlockAt program constructorEntry
      (constructorCode width constructorEntry heap.size heap.size (heap.size + 4) entry references)) :
    let within : channels ≤ ambient := by omega
    let dictionary := constructorDictionary heap originalLayout originalDictionary references
    let formula := constructorFormula heap originalLayout originalDictionary originalRepresentation.coherent references channels within
    let state := constructorState heap originalLayout originalDictionary references channels entry
      (word width heap.size :: rest) output highRegisters
    let backend := constructorFormulaBackend heap originalLayout originalDictionary originalRepresentation.coherent references channels within
    let layout := constructorDictionaryLayout heap originalLayout originalDictionary references channels
    let keep := heap.size
    let recordHeader := heap.size
    let base := state.heap.size
    let recordStart := state.heap.size + 5 * dictionary.coordinates.size + 4
    let recordEnd := Controller.Horn.NormalizeLoop.recordOffset formula.clauses.toList recordStart formula.clauses.toList.length
    ∀ (scan seedDone conflict : Nat)
      (countAt : ∀ phase : Fin 11, program[entry + phase.val]? = (scratchCountCode width)[phase.val]?)
      (allocateAt : Controller.Horn.TrackedAllocate.CodeAt program (entry + 11))
      (headersAt : ∀ phase : Fin 15, program[entry + 16 + phase.val]? = (scratchHeaderCode width)[phase.val]?)
      (endpointAt : ∀ phase : Fin 5, program[entry + 31 + phase.val]? = (scratchEndpointCode (width := width))[phase.val]?)
      (saveAt : ∀ phase : Fin 6, program[entry + 36 + phase.val]? = (saveProjectionCode (width := width))[phase.val]?)
      (normalizerAt : Controller.Horn.NormalizeLoop.CodeAt program (entry + 42) formula.clauses.toList backend)
      (indexSaveAt : Controller.Cost.ForestZeroHeaderBridge.SaveAt program (entry + 203) recordHeader)
      (indexAt : Controller.Horn.IndexScan.At (n := dictionary.coordinates.size) program (entry + 210) base recordStart)
      (indexRestoreAt : Controller.Cost.ForestZeroHeaderBridge.RestoreAt program (entry + 242))
      (captureAt : ∀ phase : Fin 6, program[entry + 245 + phase.val]? = (Controller.Cost.ForestZeroReclaim.captureCode width)[phase.val]?)
      (fullCapacity : entry + 261 < 2 ^ width)
      (setupAt : ∀ phase : Fin 10, program[entry + 251 + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := dictionary.coordinates.size) width base recordHeader recordStart scan)[phase.val]?)
      (scanAt : Controller.Horn.WorklistSeed.At (n := dictionary.coordinates.size) program base scan seedDone conflict)
      (room : state.heap.size + 5 * dictionary.coordinates.size + 4 +
      3 * formula.clauses.toList.length + (formula.clauses.toList.map List.length).sum +
      2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length < 2 ^ width)
      (scanCapacity : scan + 47 < 2 ^ width)
      (fetch : Nat)
      (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := dictionary.coordinates.size) width base fetch)[phase.val]?)
      (headCapacity : seedDone + 4 < 2 ^ width)
      (fifoDone bucket advance ready skip : Nat)
      (fetchAt : Controller.Horn.WorklistFIFO.FetchAt (n := dictionary.coordinates.size) program base fetch fifoDone bucket)
      (advanceAt : Controller.Horn.WorklistFIFO.AdvanceAt (n := dictionary.coordinates.size) program base advance fetch)
      (loopAt : Controller.Horn.WorklistBucketLoop.At program bucket advance ready)
      (readyAt : Controller.Horn.WorklistBucketReady.At (n := dictionary.coordinates.size) program base ready skip conflict bucket)
      (fetchCapacity : fetch + 14 < 2 ^ width)
      (advanceCapacity : advance + 5 < 2 ^ width)
      (bucketCapacity : bucket + 12 < 2 ^ width)
      (readyCapacity : ready + 26 < 2 ^ width)
      (projectionEntry cleanupEntry returnPc : Nat)
      (successAt : Controller.Cost.ForestZeroAnswer.SavedAt program fifoDone 1 projectionEntry)
      (conflictAt : Controller.Cost.ForestZeroAnswer.SavedAt program conflict 0 cleanupEntry)
      (successCapacity : fifoDone + 13 < 2 ^ width)
      (conflictCapacity : conflict + 13 < 2 ^ width)
      (localFit : dictionary.coordinates.size + 1 < 2 ^ width)
      (channelsFit : channels + 1 < 2 ^ width)
      (offRoom : base + 1 < 2 ^ width)
      (projectionCapacity : projectionEntry + 35 < 2 ^ width)
      (constantsAt : ∀ phase : Fin 2, program[projectionEntry + phase.val]? =
      (projectionConstantsCode width)[phase.val]?)
      (preparationAt : ∀ phase : Fin 19, program[projectionEntry + 2 + phase.val]? =
      (channelPrepareCode width)[phase.val]?)
      (emitAt : Controller.Cost.ForestZeroChannelEmit.CodeAt program (projectionEntry + 21) cleanupEntry)
      (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
      (cleanupLoop : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
      (cleanupCapacity : cleanupEntry + 7 < 2 ^ width)
      (resetCapacity : returnPc + 27 < 2 ^ width)
      (resetPrepareAt : ForestZeroCallerWiden.WidenedBlockAt program returnPc (resetPrepareCode width).toList)
      (resetLoopAt : ForestZeroCallerWiden.WidenedBlockAt program (returnPc + 15)
      (Controller.Cost.ForestZeroReset.code width (returnPc + 15)))
      (decisionCapacity : returnPc + 28 < 2 ^ width)
      (decisionAt : program[returnPc + 27]? = some (.pop 4)),
∃ answer : Bool, ∃ queue final ticks peak,
      Execution program
        (Controller.Cost.RegisterWiden.widenState
          (atState heap sourceEntry 0 originalLayout.tableBase originalLayout.inverseBase
            initialScratch rest output) highRegisters)
        final ticks peak ∧
      ticks ≤ 94 + 5 * references.length + 23 * references.flatten.length +
        86 * dictionary.coordinates.size +
        61 * (formula.clauses.toList.map List.length).sum + 125 * formula.clauses.toList.length +
        48 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length +
        4 * (recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length - keep) +
        (if answer then 13 * channels + 166 else 144) ∧
      peak ≤ max
        (18 + heap.size + 2 * (references.length + 1) + 2 * references.flatten.length +
          2 * dictionary.coordinates.size + (word width heap.size :: rest).length + output.length)
        (state.liveWords + 5 * dictionary.coordinates.size +
        3 * formula.clauses.toList.length + (formula.clauses.toList.map List.length).sum +
        2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length + channels + 8) ∧
      final.heap.size = keep ∧ final.stack = rest ∧
      final.output = (if answer then (List.finRange channels).map (fun channel =>
        Controller.Cost.ForestZeroChannelEmit.bitWord width
          (ForestZeroModelLift.lift dictionary true
            (Controller.Cost.ForestZeroChannelEmit.localValues queue)
            ⟨channel.val, by rw [ambientEq]; have := channel.isLt; omega⟩)) ++
          word width 1 :: state.output else word width 0 :: state.output) ∧
      final.pc = word width (returnPc + 28) ∧ final.halted = false ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase state.heap final.heap ∧
      (∀ coordinate : Fin ambient, final.heap[layout.tableBase + coordinate.val]? = some (word width 0)) ∧
      final.reg 4 = word width (if answer then 1 else 0) ∧
      final.reg 0 = word width 0 ∧ final.reg 1 = word width layout.tableBase ∧
      final.reg 2 = word width layout.inverseBase ∧
      (answer = true ↔ ∃ assignment, Controller.CNF.Satisfies assignment formula) ∧
      (answer = true → Controller.CNF.Satisfies (Controller.Horn.WorklistOutcome.offAssignment queue) formula ∧
        Controller.Horn.WorklistOutcome.offAssignment queue = Controller.Horn.greatestCandidate formula) ∧
      final.liveWords ≤ (Controller.Cost.RegisterWiden.widenState
        (atState heap sourceEntry 0 originalLayout.tableBase originalLayout.inverseBase
          initialScratch rest output) highRegisters).liveWords +
        1 + (if answer then channels else 0) ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame originalLayout.tableBase heap final.heap ∧
      ∃ reusableLayout : Layout ambient final.heap.size,
        reusableLayout.tableBase = originalLayout.tableBase ∧
        reusableLayout.inverseBase = originalLayout.inverseBase ∧
        Represented final.heap reusableLayout (ForestZeroCompile.empty ambient) ∧
      (∀ next : Nat, answer = false →
        QueryReady (ambient := ambient) heap originalLayout.tableBase originalLayout.inverseBase next rest
          (ForestZeroRootLoop.dispatchState final (returnPc + 28) next false)) := by
  intro within dictionary formula state backend layout keep recordHeader base recordStart recordEnd
  intro scan seedDone conflict countAt allocateAt headersAt endpointAt saveAt normalizerAt indexSaveAt indexAt indexRestoreAt captureAt fullCapacity setupAt scanAt room scanCapacity fetch headAt headCapacity fifoDone bucket advance ready skip fetchAt advanceAt loopAt readyAt fetchCapacity advanceCapacity bucketCapacity readyCapacity projectionEntry cleanupEntry returnPc successAt conflictAt successCapacity conflictCapacity localFit channelsFit offRoom projectionCapacity constantsAt preparationAt emitAt cleanupSetup cleanupLoop cleanupCapacity resetCapacity resetPrepareAt resetLoopAt decisionCapacity decisionAt
  have actualDual : Controller.Horn.DualHorn formula :=
    constructorClauses_dualHorn heap originalLayout originalDictionary originalRepresentation.coherent
      references channels within sourceDual
  have originalInputs := constructor_canonical_inputs heap originalLayout originalDictionary
    originalRepresentation references channels within
  have actualStored : Stored formula.clauses.toList backend.directory backend.source state.heap := by
    simpa only [formula, state, backend, constructorState, RegisterWiden.widenState, atState,
      constructorFormulaBackend, constructorBackend, backendLayout, constructorFormula_rows] using originalInputs.1
  have actualCursor : CursorStored backend.directory backend.directoryHeader state.heap := by
    simpa only [formula, state, backend, constructorState, RegisterWiden.widenState, atState,
      constructorFormulaBackend, constructorBackend, backendLayout, constructorFormula_rows] using originalInputs.2.1
  have actualEnd : CursorStored (backend.directory + 2 * formula.clauses.toList.length) backend.endHeader state.heap := by
    simpa only [formula, state, backend, constructorState, RegisterWiden.widenState, atState,
      constructorFormulaBackend, constructorBackend, backendLayout, constructorFormula_rows] using originalInputs.2.2
  have actualBase : backend.base = state.heap.size := rfl
  have actualRecordHeader : backend.recordHeader = keep := rfl
  have actualLocalCount : state.reg 2 = word width dictionary.coordinates.size := rfl
  have actualSourcePointer : state.reg 1 = word width state.heap.size := rfl
  have actualHeadersAbove : ∀ address ∈ [backend.recordHeader, backend.inputHeader, backend.firstHeader,
      backend.directoryHeader, backend.endHeader], backend.recordHeader ≤ address := by
    intro address member
    change address ∈ [heap.size, heap.size + 1, heap.size + 2, heap.size + 3, heap.size + 4] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> change heap.size ≤ _ <;> omega
  have actualGrowth : keep ≤ state.heap.size := constructorHeap_growth heap originalLayout originalDictionary references channels
  have actualRepresented : Represented state.heap layout dictionary :=
    constructor_dictionary_represented heap originalLayout originalDictionary originalRepresentation references channels
  have actualTableBefore : layout.tableBase + ambient ≤ keep := originalLayout.tableBound
  have actualInverseBefore : layout.inverseBase + ambient ≤ keep := originalLayout.inverseBound
  have actualChannels : state.heap[0]? = some (word width channels) :=
    (constructor_source_cell heap originalLayout originalDictionary references channels sourceEnd 0
      sourceBeforeTable sourceBeforeInverse sourceBound (by omega)).trans sourceChannel
  have actualNodes : state.heap[1]? = some (word width nodes) :=
    (constructor_source_cell heap originalLayout originalDictionary references channels sourceEnd 1
      sourceBeforeTable sourceBeforeInverse sourceBound sourceHeaderRoom).trans sourceNodes
  obtain ⟨answer, queue, final, queryTicks, queryPeak, queryTrace, queryTime, querySpace,
      heapSize, finalStack, finalOutput, finalPC, finalRunning, finalFrame, zeroTable,
      decision, zeroRegister, tableRegister, inverseRegister, meaning, greatest⟩ :=
    scratch_indexed_original_reuse_execution dictionary keep formula actualDual recordHeader recordStart recordEnd base entry scan seedDone conflict state program backend actualStored actualCursor actualEnd actualBase actualRecordHeader rfl rfl rfl rfl actualLocalCount actualSourcePointer countAt allocateAt headersAt endpointAt saveAt normalizerAt actualHeadersAbove indexSaveAt indexAt indexRestoreAt captureAt fullCapacity setupAt scanAt rfl rfl room scanCapacity actualGrowth actualGrowth fetch headAt headCapacity fifoDone bucket advance ready skip fetchAt advanceAt loopAt readyAt fetchCapacity advanceCapacity bucketCapacity readyCapacity projectionEntry cleanupEntry returnPc successAt conflictAt successCapacity conflictCapacity layout actualRepresented nodes ambientEq adjacent actualTableBefore actualInverseBefore (by omega) actualChannels actualNodes localFit channelsFit offRoom projectionCapacity constantsAt preparationAt emitAt cleanupSetup cleanupLoop cleanupCapacity rest rfl tablePositive resetCapacity resetPrepareAt resetLoopAt decisionCapacity decisionAt
  obtain ⟨constructorTicks, constructorPeak, constructorTrace, constructorTime, constructorSpace⟩ :=
    constructor_state_execution program heap originalLayout originalDictionary originalRepresentation channels
      sourceEnd references sourceReferences sourceBeforeTable sourceBeforeInverse sourceBound sourcePositive
      sourceChannel within constructorEntry entry (word width heap.size :: rest) output highRegisters
      constructorRoom ambientFits constructorCapacity constructorAt
  have prepared := reuse_entry_execution program heap sourceEntry originalLayout.tableBase
    originalLayout.inverseBase initialScratch rest output highRegisters (by omega) entryAt
  have kept := keep_cursor_execution8 program heap originalLayout channels nodes (sourceEntry + 3)
    references rest output highRegisters ambientEq sourceEndpoint (by omega) sourceChannel sourceNodes
    (by omega) (by omega) keepAt (by simpa only [Nat.add_assoc] using cursorAt)
  simp only [Nat.add_assoc] at kept
  simp only [Nat.add_assoc] at constructorTrace
  rw [originalCount, entryEq] at constructorTrace
  have readyTrace := prepared.append kept
  have queryTraceAll := constructorTrace.append queryTrace
  have joined := readyTrace.append queryTraceAll
  refine ⟨answer, queue, final, 15 + (constructorTicks + queryTicks),
    max (max (10 + heap.size + rest.length + output.length)
      (11 + heap.size + rest.length + output.length)) (max constructorPeak queryPeak),
    (by simpa only [← Nat.add_assoc] using joined), ?_, ?_, heapSize, finalStack, finalOutput, finalPC, finalRunning, finalFrame,
    zeroTable, decision, zeroRegister, tableRegister, inverseRegister, meaning, greatest, ?_, ?_, ?_⟩
  · simp only [dictionary, constructorDictionary] at constructorTime queryTime ⊢
    omega
  · have constructorBelow := Nat.le_max_left
        (18 + heap.size + 2 * (references.length + 1) + 2 * references.flatten.length +
          2 * dictionary.coordinates.size + (word width heap.size :: rest).length + output.length)
        (state.liveWords + 5 * dictionary.coordinates.size + 3 * formula.clauses.toList.length +
          (formula.clauses.toList.map List.length).sum +
          2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length + channels + 8)
    have combined := max_le_max constructorSpace querySpace
    simp only [dictionary, constructorDictionary] at constructorSpace querySpace constructorBelow combined ⊢
    simp only [List.length_cons] at constructorBelow combined ⊢
    omega
  · unfold State.liveWords
    rw [heapSize, finalStack, finalOutput]
    cases answer <;> simp [keep, state, constructorState, RegisterWiden.widenState, atState] <;> omega
  · have before := constructor_prefix heap originalLayout originalDictionary references channels adjacent
    have after : ForestZeroBackendFrame.PrefixFrame originalLayout.tableBase
        (constructorHeap heap originalLayout originalDictionary references channels) final.heap := by
      simpa only [layout, constructorDictionaryLayout, state, constructorState,
        RegisterWiden.widenState, atState] using finalFrame
    exact ForestZeroBackendFrame.trans before after
  · let reusableLayout : Layout ambient final.heap.size :=
      { tableBase := originalLayout.tableBase
        inverseBase := originalLayout.inverseBase
        tableBound := by rw [heapSize]; exact originalLayout.tableBound
        inverseBound := by rw [heapSize]; exact originalLayout.inverseBound
        disjoint := originalLayout.disjoint }
    have actualZero : ∀ coordinate : Fin ambient,
        final.heap[originalLayout.tableBase + coordinate.val]? = some (word width 0) := by
      intro coordinate
      simpa only [layout, constructorDictionaryLayout] using zeroTable coordinate
    refine ⟨reusableLayout, rfl, rfl,
      empty_dictionary_from_zero_table final.heap reusableLayout actualZero, ?_⟩
    intro next failed
    have originalFrame : ForestZeroBackendFrame.PrefixFrame originalLayout.tableBase heap final.heap := by
      have before := constructor_prefix heap originalLayout originalDictionary references channels adjacent
      have after : ForestZeroBackendFrame.PrefixFrame originalLayout.tableBase
          (constructorHeap heap originalLayout originalDictionary references channels) final.heap := by
        simpa only [layout, constructorDictionaryLayout, state, constructorState,
          RegisterWiden.widenState, atState] using finalFrame
      exact ForestZeroBackendFrame.trans before after
    exact failed_query_dispatch_ready heap originalLayout.tableBase originalLayout.inverseBase
      (returnPc + 28) next rest final heapSize originalFrame actualZero finalStack zeroRegister
      (by simpa only [layout, constructorDictionaryLayout] using tableRegister)
      (by simpa only [layout, constructorDictionaryLayout] using inverseRegister)


/-- Indexing charges retained incidences to original signed source occurrences,
including repeated rows and literals. -/
theorem source_incidence_bound (clauses : List (Clause (Fin n))) (start : Nat) :
    (Controller.Horn.IndexScan.occurrences clauses start).length ≤ (clauses.map List.length).sum := by
  induction clauses generalizing start with
  | nil => simp [Controller.Horn.IndexScan.occurrences]
  | cons clause rest ih =>
    have body := Controller.Horn.NormalizeLoop.compiled_body_le clause
    have tail := ih (start + 3 + (Controller.Horn.Worklist.compileClause clause).positives.length)
    simp only [Controller.Horn.IndexScan.occurrences, List.length_append, List.length_map,
      List.map_cons, List.sum_cons]
    omega

/-- Each packed row contributes three actual headers and at most one stored
body word per original literal occurrence. -/
theorem source_record_end_bound (clauses : List (Clause (Fin n))) (start : Nat) :
    Controller.Horn.NormalizeLoop.recordOffset clauses start clauses.length ≤
      start + 3 * clauses.length + (clauses.map List.length).sum := by
  have stored := Controller.Horn.NormalizeLoop.wordSuffix_bound clauses 0
  simpa only [Controller.Horn.NormalizeLoop.recordOffset, List.take_length,
    Controller.Horn.NormalizeLoop.wordSuffix, Controller.Horn.NormalizeLoop.literalSuffix,
    List.drop_zero, Nat.add_assoc] using Nat.add_le_add_left stored start

/-- The actual per-query constructor emits a linear instruction list. No
ambient-channel-sized initialization or emission block is duplicated. -/
theorem constructorCode_length (width base protectedEnd recordHeader endHeader returnPC : Nat)
    (references : List (List (Reference ambient))) :
    (constructorCode width base protectedEnd recordHeader endHeader returnPC references).length ≤
      102 + 5 * references.length + 28 * references.flatten.length := by
  have source := ForestZeroQueryCaller.queryCode_length width base protectedEnd (reservedReferences references)
  simp only [constructorCode, List.length_append, code_length]
  simp only [reservedReferences_length, reservedReferences_flatten] at source
  omega

/-- Source-row budgets for the actual full query exclude ambient-channel
emission on failures. The channel term is charged only by a successful query. -/
theorem query_time_budget (rows literals locals packedRows packedLiterals incidences count channels : Nat)
    (answer : Bool) (localsBound : locals ≤ literals)
    (rowsBound : packedRows ≤ rows + 1)
    (literalsBound : packedLiterals ≤ literals + locals)
    (incidenceBound : incidences ≤ packedLiterals)
    (countBound : count ≤ 14 + 5 * rows + 5 * literals + 10 * locals) :
    94 + 5 * rows + 23 * literals + 86 * locals + 61 * packedLiterals +
      125 * packedRows + 48 * incidences + 4 * count +
      (if answer then 13 * channels + 166 else 144) ≤
      150 * rows + 387 * literals + 441 + (if answer then 13 * channels else 0) := by
  cases answer <;> simp <;> omega

/-- Query-local rows and scratch determine the peak; the ambient shared table
is already included in initialLive and is not reallocated for each query. -/
theorem query_peak_budget (initialLive rows literals locals packedRows packedLiterals incidences channels : Nat)
    (localsBound : locals ≤ literals) (rowsBound : packedRows ≤ rows + 1)
    (literalsBound : packedLiterals ≤ literals + locals)
    (incidenceBound : incidences ≤ packedLiterals)
    (constructedGrowth : constructedLive ≤ initialLive + 9 + 2 * rows + 2 * literals + 2 * locals) :
    max (initialLive + 12 + 2 * rows + 2 * literals + 2 * locals)
      (constructedLive + 5 * locals + 3 * packedRows + packedLiterals + 2 * incidences + channels + 8) ≤
      initialLive + 5 * rows + 15 * literals + channels + 20 := by
  apply max_le
  · omega
  · omega

/-- The executed nonemptiness branch appends channel pairs only when every
channel already has an allocated local index. It never adds an ambient scan
term to the constructor's word or scratch bound. -/
theorem constructor_heap_local_bound (heap : Array (Word width))
    (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (coherent : Coherent dictionary) (references : List (List (Reference ambient)))
    (channels : Nat) (within : channels ≤ ambient) :
    (constructorHeap heap layout dictionary references channels).size ≤
      heap.size + 7 + 2 * references.length + 2 * references.flatten.length +
        2 * (constructorDictionary heap layout dictionary references).coordinates.size := by
  rw [constructorHeap_size]
  split_ifs with covered
  · have slots := constructor_covered_slots dictionary coherent references channels within covered
    have compiledCoherent := (rows_dictionary dictionary coherent
      (ForestZeroAssembly.originalRows (reservedReferences references))).1
    have channelBound := ForestZeroPositive.covered_count
      (constructorDictionary heap layout dictionary references) compiledCoherent channels within slots
    omega
  · omega

/-- Actual packed-record end and retained incidences bound the physically
captured allocation count for this constructor, including its optional row. -/
theorem constructor_reclaimed_count_bound (heap : Array (Word width))
    (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (coherent : Coherent dictionary) (references : List (List (Reference ambient)))
    (channels : Nat) (within : channels ≤ ambient) :
    let compiled := constructorDictionary heap layout dictionary references
    let clauses := constructorClauses heap layout dictionary coherent references channels within
    let start := (constructorHeap heap layout dictionary references channels).size + 5 * compiled.coordinates.size + 4
    Controller.Horn.NormalizeLoop.recordOffset clauses start clauses.length +
      2 * (Controller.Horn.IndexScan.occurrences clauses start).length - heap.size ≤
      14 + 5 * references.length + 5 * references.flatten.length + 10 * compiled.coordinates.size := by
  intro compiled clauses start
  have heapBound := constructor_heap_local_bound heap layout dictionary coherent references channels within
  have rowsEq := constructorClauses_length heap layout dictionary coherent references channels within
  have rowsBound : clauses.length ≤ references.length + 1 := by
    dsimp only [clauses]
    rw [rowsEq]
    split_ifs <;> omega
  have literalsBound := constructorClauses_profile_bound heap layout dictionary coherent references channels within
  have incidenceBound := source_incidence_bound clauses start
  have recordsBound := source_record_end_bound clauses start
  change (clauses.map List.length).sum ≤ references.flatten.length + compiled.coordinates.size at literalsBound
  change (constructorHeap heap layout dictionary references channels).size ≤
    heap.size + 7 + 2 * references.length + 2 * references.flatten.length + 2 * compiled.coordinates.size at heapBound
  dsimp only [start] at incidenceBound recordsBound ⊢
  omega

/-- This projection counts the two retained words at the source constructor's
full-query endpoint when its caller stack already contains saved keep. -/
theorem constructorState_liveWords (heap : Array (Word width))
    (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (references : List (List (Reference ambient))) (channels entry : Nat)
    (stack output : List (Word width)) (saved : Fin 8 → Word width) :
    (constructorState heap layout dictionary references channels entry stack output saved).liveWords =
      10 + (constructorHeap heap layout dictionary references channels).size + stack.length + output.length := by
  simp only [constructorState, RegisterWiden.widenState, atState, State.liveWords, List.length_cons]
  omega

/-- All scalar charges are obtained from the actual constructor rows and
captured physical allocation extent, with no ambient-size term on failure. -/
theorem constructor_full_query_budget (heap : Array (Word width))
    (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (coherent : Coherent dictionary) (references : List (List (Reference ambient)))
    (channels : Nat) (within : channels ≤ ambient) (originalCount : dictionary.coordinates.size = 0)
    (entry sourceEntry scratch : Nat) (rest output : List (Word width)) (saved : Fin 8 → Word width)
    (answer : Bool) :
    let compiled := constructorDictionary heap layout dictionary references
    let clauses := constructorClauses heap layout dictionary coherent references channels within
    let state := constructorState heap layout dictionary references channels entry (word width heap.size :: rest) output saved
    let start := state.heap.size + 5 * compiled.coordinates.size + 4
    let incidences := (Controller.Horn.IndexScan.occurrences clauses start).length
    let count := Controller.Horn.NormalizeLoop.recordOffset clauses start clauses.length + 2 * incidences - heap.size
    let initial := RegisterWiden.widenState (atState heap sourceEntry 0 layout.tableBase layout.inverseBase scratch rest output) saved
    (94 + 5 * references.length + 23 * references.flatten.length + 86 * compiled.coordinates.size +
      61 * (clauses.map List.length).sum + 125 * clauses.length + 48 * incidences + 4 * count +
      (if answer then 13 * channels + 166 else 144) ≤
        150 * references.length + 387 * references.flatten.length + 441 + (if answer then 13 * channels else 0)) ∧
    (max (18 + heap.size + 2 * (references.length + 1) + 2 * references.flatten.length +
        2 * compiled.coordinates.size + (word width heap.size :: rest).length + output.length)
      (state.liveWords + 5 * compiled.coordinates.size + 3 * clauses.length +
        (clauses.map List.length).sum + 2 * incidences + channels + 8) ≤
        initial.liveWords + 5 * references.length + 15 * references.flatten.length + channels + 20) := by
  intro compiled clauses state start incidences count initial
  have localBound := constructorDictionary_size_bound heap layout dictionary references
  rw [originalCount, Nat.zero_add] at localBound
  have rowsEq := constructorClauses_length heap layout dictionary coherent references channels within
  have rowsBound : clauses.length ≤ references.length + 1 := by
    dsimp only [clauses]
    rw [rowsEq]
    split_ifs <;> omega
  have literalsBound := constructorClauses_profile_bound heap layout dictionary coherent references channels within
  have incidenceBound := source_incidence_bound clauses start
  have countBound := constructor_reclaimed_count_bound heap layout dictionary coherent references channels within
  change compiled.coordinates.size ≤ references.flatten.length at localBound
  change (clauses.map List.length).sum ≤ references.flatten.length + compiled.coordinates.size at literalsBound
  change incidences ≤ (clauses.map List.length).sum at incidenceBound
  change count ≤ 14 + 5 * references.length + 5 * references.flatten.length + 10 * compiled.coordinates.size at countBound
  have heapBound := constructor_heap_local_bound heap layout dictionary coherent references channels within
  have stateLive := constructorState_liveWords heap layout dictionary references channels entry
    (word width heap.size :: rest) output saved
  have initialLive : initial.liveWords = 9 + heap.size + rest.length + output.length := by
    simp only [initial, RegisterWiden.widenState, atState, State.liveWords]
    omega
  have growth : state.liveWords ≤ initial.liveWords + 9 + 2 * references.length +
      2 * references.flatten.length + 2 * compiled.coordinates.size := by
    change state.liveWords = _ at stateLive
    simp only [List.length_cons] at stateLive
    change (constructorHeap heap layout dictionary references channels).size ≤
      heap.size + 7 + 2 * references.length + 2 * references.flatten.length + 2 * compiled.coordinates.size at heapBound
    omega
  constructor
  · exact query_time_budget _ _ _ _ _ _ _ _ answer localBound rowsBound literalsBound incidenceBound countBound
  · have budget := query_peak_budget initial.liveWords references.length references.flatten.length
      compiled.coordinates.size clauses.length (clauses.map List.length).sum incidences channels
      localBound rowsBound literalsBound incidenceBound growth
    convert budget using 1 <;> simp only [initialLive, List.length_cons] <;> omega

/-- Fetched blocks and bounded source cells for one declared occurrence.
This record contains no execution, semantic model, or supplied query layout. -/
structure SourceQueryPlan {width channels ambient : Nat}
    (program : Program width 8) (initial : State width 8)
    (sharedLayout : Layout ambient initial.heap.size)
    (references : List (List (Reference ambient))) (sourceEnd nodes sourceEntry : Nat)
    (rest : List (Word width)) (within : channels ≤ ambient)
    (dispatchEntry nextEntry : Nat) where
  sourceReferences : ∀ reference ∈ references.flatten,
          Controller.Cost.ForestZeroEmit.StoredReference (initial.heap) channels sourceEnd reference
  sourceBeforeTable : sourceEnd ≤ (sharedLayout).tableBase
  sourceBeforeInverse : sourceEnd ≤ (sharedLayout).inverseBase
  sourceBound : sourceEnd ≤ (initial.heap).size
  sourcePositive : 0 < sourceEnd
  sourceChannel : (initial.heap)[0]? = some (word width channels)
  sourceNodes : (initial.heap)[1]? = some (word width nodes)
  ambientEq : ambient = channels + nodes
  adjacent : (sharedLayout).inverseBase = (sharedLayout).tableBase + ambient
  tablePositive : 0 < (sharedLayout).tableBase
  sourceHeaderRoom : 1 < sourceEnd
  sourceDual : Controller.Horn.DualHorn
          (ofClauses (ForestZeroAssembly.originalRows (reservedReferences references)))
  constructorEntry : Nat
  entry : Nat
  entryEq : constructorEntry = sourceEntry + 15
  sourceEndpoint : (initial.heap).size = (sharedLayout).inverseBase + ambient
  entryCapacity : sourceEntry + 15 < 2 ^ width
  entryAt : ∀ phase : Fin 3, program[sourceEntry + phase.val]? = (reuseEntryCode width)[phase.val]?
  keepAt : ForestZeroCallerWiden.WidenedBlockAt program (sourceEntry + 3) (keepCode width)
  cursorAt : program[sourceEntry + 14]? = some (.constant 0
          (word width ((initial.heap).size + 5 + 2 * (references.length + 1))))
  constructorRoom : (initial.heap).size + 5 + 2 * (references.length + 1) +
          2 * references.flatten.length + 2 * ambient < 2 ^ width
  ambientFits : ambient + 1 < 2 ^ width
  constructorCapacity : constructorEntry +
          (constructorCode width constructorEntry (initial.heap).size (initial.heap).size ((initial.heap).size + 4) entry references).length < 2 ^ width
  constructorAt : ForestZeroCallerWiden.WidenedBlockAt program constructorEntry
          (constructorCode width constructorEntry (initial.heap).size (initial.heap).size ((initial.heap).size + 4) entry references)
  scan : Nat
  seedDone : Nat
  conflict : Nat
  countAt : ∀ phase : Fin 11, program[entry + phase.val]? = (scratchCountCode width)[phase.val]?
  allocateAt : Controller.Horn.TrackedAllocate.CodeAt program (entry + 11)
  headersAt : ∀ phase : Fin 15, program[entry + 16 + phase.val]? = (scratchHeaderCode width)[phase.val]?
  endpointAt : ∀ phase : Fin 5, program[entry + 31 + phase.val]? = (scratchEndpointCode (width := width))[phase.val]?
  saveAt : ∀ phase : Fin 6, program[entry + 36 + phase.val]? = (saveProjectionCode (width := width))[phase.val]?
  normalizerAt : Controller.Horn.NormalizeLoop.CodeAt program (entry + 42) (constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) references channels within).clauses.toList (constructorFormulaBackend initial.heap sharedLayout (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) references channels within)
  indexSaveAt : Controller.Cost.ForestZeroHeaderBridge.SaveAt program (entry + 203) (initial.heap.size)
  indexAt : Controller.Horn.IndexScan.At (n := (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size) program (entry + 210) ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels).size) ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels).size + 5 * (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size + 4)
  indexRestoreAt : Controller.Cost.ForestZeroHeaderBridge.RestoreAt program (entry + 242)
  captureAt : ∀ phase : Fin 6, program[entry + 245 + phase.val]? = (Controller.Cost.ForestZeroReclaim.captureCode width)[phase.val]?
  fullCapacity : entry + 261 < 2 ^ width
  setupAt : ∀ phase : Fin 10, program[entry + 251 + phase.val]? =
          (Controller.Cost.ForestZeroSeedSetup.code (n := (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size) width ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels).size) (initial.heap.size) ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels).size + 5 * (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size + 4) scan)[phase.val]?
  scanAt : Controller.Horn.WorklistSeed.At (n := (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size) program ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels).size) scan seedDone conflict
  room : (constructorState initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels entry (word width initial.heap.size :: rest) initial.output initial.reg).heap.size + 5 * (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size + 4 +
          3 * (constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) references channels within).clauses.toList.length + ((constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) references channels within).clauses.toList.map List.length).sum +
          2 * (Controller.Horn.IndexScan.occurrences (constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) references channels within).clauses.toList ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels).size + 5 * (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size + 4)).length < 2 ^ width
  scanCapacity : scan + 47 < 2 ^ width
  fetch : Nat
  headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
          (Controller.Horn.WorklistAccept.headSetupCode (n := (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size) width ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels).size) fetch)[phase.val]?
  headCapacity : seedDone + 4 < 2 ^ width
  fifoDone : Nat
  bucket : Nat
  advance : Nat
  ready : Nat
  skip : Nat
  fetchAt : Controller.Horn.WorklistFIFO.FetchAt (n := (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size) program ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels).size) fetch fifoDone bucket
  advanceAt : Controller.Horn.WorklistFIFO.AdvanceAt (n := (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size) program ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels).size) advance fetch
  loopAt : Controller.Horn.WorklistBucketLoop.At program bucket advance ready
  readyAt : Controller.Horn.WorklistBucketReady.At (n := (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size) program ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels).size) ready skip conflict bucket
  fetchCapacity : fetch + 14 < 2 ^ width
  advanceCapacity : advance + 5 < 2 ^ width
  bucketCapacity : bucket + 12 < 2 ^ width
  readyCapacity : ready + 26 < 2 ^ width
  projectionEntry : Nat
  cleanupEntry : Nat
  returnPc : Nat
  successAt : Controller.Cost.ForestZeroAnswer.SavedAt program fifoDone 1 projectionEntry
  conflictAt : Controller.Cost.ForestZeroAnswer.SavedAt program conflict 0 cleanupEntry
  successCapacity : fifoDone + 13 < 2 ^ width
  conflictCapacity : conflict + 13 < 2 ^ width
  localFit : (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size + 1 < 2 ^ width
  channelsFit : channels + 1 < 2 ^ width
  offRoom : ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels).size) + 1 < 2 ^ width
  projectionCapacity : projectionEntry + 35 < 2 ^ width
  constantsAt : ∀ phase : Fin 2, program[projectionEntry + phase.val]? =
          (projectionConstantsCode width)[phase.val]?
  preparationAt : ∀ phase : Fin 19, program[projectionEntry + 2 + phase.val]? =
          (channelPrepareCode width)[phase.val]?
  emitAt : Controller.Cost.ForestZeroChannelEmit.CodeAt program (projectionEntry + 21) cleanupEntry
  cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
          (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?
  cleanupLoop : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc
  cleanupCapacity : cleanupEntry + 7 < 2 ^ width
  resetCapacity : returnPc + 27 < 2 ^ width
  resetPrepareAt : ForestZeroCallerWiden.WidenedBlockAt program returnPc (resetPrepareCode width).toList
  resetLoopAt : ForestZeroCallerWiden.WidenedBlockAt program (returnPc + 15)
          (Controller.Cost.ForestZeroReset.code width (returnPc + 15))
  decisionCapacity : returnPc + 28 < 2 ^ width
  decisionAt : program[returnPc + 27]? = some (.pop 4)
  dispatchEq : returnPc + 28 = dispatchEntry
  dispatchCapacity : dispatchEntry + 2 < 2 ^ width
  dispatchAt : ∀ phase : Fin 2, program[dispatchEntry + phase.val]? =
    (ForestZeroRootLoop.dispatchCode width nextEntry)[phase.val]?

/-- The physical channel output is the lift of this execution's actual
terminal FIFO model, with TRUE only on unallocated original coordinates. -/
def QueryChannelWitness (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient)
    (observed : List (Word width)) : Prop :=
  let dictionary := constructorDictionary heap layout (ForestZeroCompile.empty ambient) references
  let formula := constructorFormula heap layout (ForestZeroCompile.empty ambient)
    (ForestZeroCompile.empty_coherent ambient) references channels within
  ∃ queue : List (Fin dictionary.coordinates.size), ∃ previous : List (Word width),
    Controller.CNF.Satisfies (Controller.Horn.WorklistOutcome.offAssignment queue) formula ∧
    Controller.Horn.WorklistOutcome.offAssignment queue = Controller.Horn.greatestCandidate formula ∧
    observed = (List.finRange channels).map (fun channel =>
      ForestZeroChannelEmit.bitWord width (ForestZeroModelLift.lift dictionary true
        (ForestZeroChannelEmit.localValues queue) ⟨channel.val, lt_of_lt_of_le channel.isLt within⟩)) ++
      word width 1 :: previous

/-- Formula coordinates and rows depend on the source occurrences, not on
inverse-array values left by a preceding touched-only reset. -/
theorem constructorFormula_heap_irrel (first second : Array (Word width))
    (firstLayout : Layout ambient first.size) (secondLayout : Layout ambient second.size)
    (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient) :
    constructorFormula first firstLayout dictionary coherent references channels within =
      constructorFormula second secondLayout dictionary coherent references channels within := rfl

/-- The ready source layout is retained at the actual next-query heap size. -/
def QueryReady.current_layout
    {sourceHeap : Array (Word width)} {entry : Nat} {rest : List (Word width)} {state : State width 8}
    (layout : Layout ambient sourceHeap.size)
    (ready : QueryReady (ambient := ambient) sourceHeap layout.tableBase layout.inverseBase entry rest state) :
    Layout ambient state.heap.size where
  tableBase := layout.tableBase
  inverseBase := layout.inverseBase
  tableBound := by rw [ready.heapSize]; exact layout.tableBound
  inverseBound := by rw [ready.heapSize]; exact layout.inverseBound
  disjoint := layout.disjoint

/-- Two actual source-prefix frames compose across a failed occurrence. -/
theorem QueryReady.rebase
    {sourceHeap middle : Array (Word width)} {tableBase inverseBase entry : Nat}
    {rest : List (Word width)} {state : State width 8}
    (ready : QueryReady (ambient := ambient) middle tableBase inverseBase entry rest state)
    (sameSize : middle.size = sourceHeap.size)
    (before : ForestZeroBackendFrame.PrefixFrame tableBase sourceHeap middle) :
    QueryReady (ambient := ambient) sourceHeap tableBase inverseBase entry rest state :=
  ⟨ready.heapSize.trans sameSize, ForestZeroBackendFrame.trans before ready.sourceFrame,
    ready.zeroTable, ready.stack, ready.position, ready.running,
    ready.zeroRegister, ready.tableRegister, ready.inverseRegister⟩

/-- The stored physical blocks run the source constructor, backend and reset
from the recovered entry ABI. No callback execution premise occurs here. -/
theorem SourceQueryPlan.execute {width channels ambient : Nat}
    (program : Program width 8) (initial : State width 8) (sourceHeap : Array (Word width))
    (sharedLayout : Layout ambient initial.heap.size)
    (references : List (List (Reference ambient))) (sourceEnd nodes sourceEntry : Nat)
    (rest : List (Word width)) (within : channels ≤ ambient) (dispatchEntry nextEntry : Nat)
    (plan : SourceQueryPlan program initial sharedLayout references sourceEnd nodes sourceEntry rest within dispatchEntry nextEntry)
    (initialReady : QueryReady (ambient := ambient) sourceHeap sharedLayout.tableBase sharedLayout.inverseBase sourceEntry rest initial) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program initial final ticks peak ∧
      final.pc = word width dispatchEntry ∧ final.halted = false ∧
      final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ 150 * references.length + 387 * references.flatten.length + 441 +
        (if answer then 13 * channels else 0) ∧
      peak ≤ initial.liveWords + 5 * references.length + 15 * references.flatten.length + channels + 20 ∧
      final.liveWords ≤ initial.liveWords + 1 + (if answer then channels else 0) ∧
      (answer = true ↔ Controller.CNF.Satisfiable
        (constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient)
          (ForestZeroCompile.empty_coherent ambient) references channels within)) ∧
      (answer = true → QueryChannelWitness initial.heap sharedLayout references channels within final.output) ∧
      (answer = false → QueryReady (ambient := ambient) sourceHeap sharedLayout.tableBase sharedLayout.inverseBase nextEntry rest
        (ForestZeroRootLoop.dispatchState final dispatchEntry nextEntry false)) ∧
      dispatchEntry + 2 < 2 ^ width ∧
      (∀ phase : Fin 2, program[dispatchEntry + phase.val]? =
        (ForestZeroRootLoop.dispatchCode width nextEntry)[phase.val]?) := by
  have represented : Represented initial.heap sharedLayout (ForestZeroCompile.empty ambient) :=
    empty_dictionary_from_zero_table initial.heap sharedLayout initialReady.zeroTable
  have initialEq := initialReady.entry_state
  obtain ⟨answer, queue, final, ticks, peak, trace, timeBound, spaceBound, heapSize, finalStack,
      finalOutput, finalPC, finalRunning, originalFrame, zeroTable, decision, zeroRegister,
      tableRegister, inverseRegister, meaning, greatest, finalLive, sourceFrame,
      actualLayout, actualTable, actualInverse, emptyRepresentation, nextReady⟩ :=
    source_constructor_original_reuse_execution initial.heap sharedLayout (ForestZeroCompile.empty ambient) represented references sourceEnd nodes plan.sourceReferences plan.sourceBeforeTable plan.sourceBeforeInverse plan.sourceBound plan.sourcePositive plan.sourceChannel plan.sourceNodes plan.ambientEq plan.adjacent plan.tablePositive plan.sourceHeaderRoom plan.sourceDual program sourceEntry plan.constructorEntry plan.entry plan.entryEq (by rfl) plan.sourceEndpoint (initial.reg 3).val plan.entryCapacity plan.entryAt plan.keepAt plan.cursorAt rest initial.output initial.reg plan.constructorRoom plan.ambientFits plan.constructorCapacity plan.constructorAt plan.scan plan.seedDone plan.conflict plan.countAt plan.allocateAt plan.headersAt plan.endpointAt plan.saveAt plan.normalizerAt plan.indexSaveAt plan.indexAt plan.indexRestoreAt plan.captureAt plan.fullCapacity plan.setupAt plan.scanAt plan.room plan.scanCapacity plan.fetch plan.headAt plan.headCapacity plan.fifoDone plan.bucket plan.advance plan.ready plan.skip plan.fetchAt plan.advanceAt plan.loopAt plan.readyAt plan.fetchCapacity plan.advanceCapacity plan.bucketCapacity plan.readyCapacity plan.projectionEntry plan.cleanupEntry plan.returnPc plan.successAt plan.conflictAt plan.successCapacity plan.conflictCapacity plan.localFit plan.channelsFit plan.offRoom plan.projectionCapacity plan.constantsAt plan.preparationAt plan.emitAt plan.cleanupSetup plan.cleanupLoop plan.cleanupCapacity plan.resetCapacity plan.resetPrepareAt plan.resetLoopAt plan.decisionCapacity plan.decisionAt
  rw [initialEq] at trace finalLive
  have budgets := constructor_full_query_budget initial.heap sharedLayout (ForestZeroCompile.empty ambient)
    (ForestZeroCompile.empty_coherent ambient) references channels within rfl plan.entry sourceEntry
    (initial.reg 3).val rest initial.output initial.reg answer
  rw [initialEq] at budgets
  simp only [constructorFormula_rows] at timeBound spaceBound
  refine ⟨answer, final, ticks, peak, trace, ?_, finalRunning, decision,
    timeBound.trans budgets.1, spaceBound.trans budgets.2, finalLive, meaning, ?_, ?_,
    plan.dispatchCapacity, plan.dispatchAt⟩
  · simpa only [plan.dispatchEq] using finalPC
  · intro accepted
    refine ⟨queue, initial.output, (greatest accepted).1, (greatest accepted).2, ?_⟩
    rw [accepted] at finalOutput
    simpa [constructorState, RegisterWiden.widenState, atState] using finalOutput
  · intro rejected
    exact (nextReady nextEntry rejected).rebase initialReady.heapSize initialReady.sourceFrame

/-- Declared positions index queries, so repeated root labels keep distinct
resident blocks and source incidence charges. Physical plans supply fetched
instructions and source-cell proofs, not callback executions. -/
theorem occurrence_query_contract {width channels ambient : Nat}
    (program : Program width 8) (sourceHeap : Array (Word width))
    (layout : Layout ambient sourceHeap.size)
    (queries : List (List (List (Reference ambient)))) (sourceEnd nodes : Nat)
    (rest : List (Word width)) (within : channels ≤ ambient)
    (resume : List (Fin queries.length) → Nat) (dispatch : Fin queries.length → Nat) (scratch : Nat)
    (scratchBound : ∀ position : Fin queries.length,
      5 * queries[position].length + 15 * queries[position].flatten.length + channels + 20 ≤ scratch)
    (plans : ∀ (position : Fin queries.length) (tail : List (Fin queries.length)) (state : State width 8),
      ForestZeroRootLoop.TailOf (List.finRange queries.length) (position :: tail) →
      ∀ initialReady : QueryReady (ambient := ambient) sourceHeap layout.tableBase layout.inverseBase
          (resume (position :: tail)) rest state,
      SourceQueryPlan program state (initialReady.current_layout layout) queries[position] sourceEnd nodes
        (resume (position :: tail)) rest within (dispatch position) (resume tail)) :
    ForestZeroRootLoop.QueryContract program (List.finRange queries.length)
      (fun remaining state => QueryReady (ambient := ambient) sourceHeap layout.tableBase layout.inverseBase
        (resume remaining) rest state)
      (fun position => Controller.CNF.Satisfiable (constructorFormula sourceHeap layout
        (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) queries[position] channels within))
      (fun position observed => QueryChannelWitness sourceHeap layout queries[position] channels within observed)
      resume dispatch
      (fun position => 150 * queries[position].length + 387 * queries[position].flatten.length + 441)
      scratch (13 * channels) channels := by
  intro position tail state suffix initialReady
  let actualLayout := initialReady.current_layout layout
  have actualReady : QueryReady (ambient := ambient) sourceHeap actualLayout.tableBase actualLayout.inverseBase
      (resume (position :: tail)) rest state := initialReady
  obtain ⟨answer, final, ticks, peak, trace, finalPC, finalRunning, decision, timeBound,
      spaceBound, finalLive, meaning, witnessed, failedReady, dispatchCapacity, dispatchAt⟩ :=
    SourceQueryPlan.execute program state sourceHeap actualLayout queries[position] sourceEnd nodes
      (resume (position :: tail)) rest within (dispatch position) (resume tail)
      (plans position tail state suffix initialReady) actualReady
  refine ⟨answer, final, ticks, peak, trace, finalPC, finalRunning, decision, timeBound,
    ?_, finalLive, ?_, ?_, failedReady, dispatchCapacity, dispatchAt⟩
  · have localScratch := scratchBound position
    omega
  · have same := constructorFormula_heap_irrel state.heap sourceHeap actualLayout layout
      (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) queries[position] channels within
    rw [same] at meaning
    exact meaning
  · exact witnessed

/-- The complete first-success consumer invokes actual per-occurrence source
constructors through their physical instruction plans. The Boolean decision
is returned in register four, including the empty stream; a successful stream
also returns the lifted original-channel model in the emitted prefix. -/
theorem source_first_success_execution {width channels ambient : Nat}
    (program : Program width 8) (sourceHeap : Array (Word width))
    (layout : Layout ambient sourceHeap.size)
    (queries : List (List (List (Reference ambient)))) (sourceEnd nodes : Nat)
    (rest : List (Word width)) (within : channels ≤ ambient)
    (resume : List (Fin queries.length) → Nat) (dispatch : Fin queries.length → Nat) (scratch : Nat)
    (scratchBound : ∀ position : Fin queries.length,
      5 * queries[position].length + 15 * queries[position].flatten.length + channels + 20 ≤ scratch)
    (plans : ∀ (position : Fin queries.length) (tail : List (Fin queries.length)) (state : State width 8),
      ForestZeroRootLoop.TailOf (List.finRange queries.length) (position :: tail) →
      ∀ initialReady : QueryReady (ambient := ambient) sourceHeap layout.tableBase layout.inverseBase
          (resume (position :: tail)) rest state,
      SourceQueryPlan program state (initialReady.current_layout layout) queries[position] sourceEnd nodes
        (resume (position :: tail)) rest within (dispatch position) (resume tail))
    (emptyFits : resume [] + 2 < 2 ^ width)
    (emptyAt : ∀ phase : Fin 2, program[resume [] + phase.val]? =
      (ForestZeroRootLoop.exhaustedCode width)[phase.val]?)
    (initial : State width 8)
    (initialReady : QueryReady (ambient := ambient) sourceHeap layout.tableBase layout.inverseBase
      (resume (List.finRange queries.length)) rest initial) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program initial final ticks peak ∧ final.halted = true ∧
      final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ 150 * (queries.map List.length).sum +
        387 * (queries.map (fun rows => rows.flatten.length)).sum + 442 * queries.length + 13 * channels + 2 ∧
      peak ≤ initial.liveWords + scratch + queries.length + channels + 1 ∧
      (answer = true ↔ ∃ position : Fin queries.length,
        Controller.CNF.Satisfiable (constructorFormula sourceHeap layout (ForestZeroCompile.empty ambient)
          (ForestZeroCompile.empty_coherent ambient) queries[position] channels within)) ∧
      (answer = true → ∃ position : Fin queries.length,
        Controller.CNF.Satisfiable (constructorFormula sourceHeap layout (ForestZeroCompile.empty ambient)
          (ForestZeroCompile.empty_coherent ambient) queries[position] channels within) ∧
        QueryChannelWitness sourceHeap layout queries[position] channels within final.output) := by
  let actualQueries := List.finRange queries.length
  let ready := fun remaining state => QueryReady (ambient := ambient) sourceHeap layout.tableBase layout.inverseBase
    (resume remaining) rest state
  let feasible := fun position : Fin queries.length => Controller.CNF.Satisfiable
    (constructorFormula sourceHeap layout (ForestZeroCompile.empty ambient)
      (ForestZeroCompile.empty_coherent ambient) queries[position] channels within)
  let witnessed := fun (position : Fin queries.length) observed => QueryChannelWitness sourceHeap layout queries[position] channels within observed
  let work := fun position : Fin queries.length => 150 * queries[position].length +
    387 * queries[position].flatten.length + 441
  have contract := occurrence_query_contract program sourceHeap layout queries sourceEnd nodes rest within
    resume dispatch scratch scratchBound plans
  have emptyReady : ∀ state, ready [] state → state.pc = word width (resume []) ∧ state.halted = false := by
    intro state prepared
    exact ⟨prepared.position, prepared.running⟩
  obtain ⟨answer, final, ticks, peak, trace, halted, decision, timeBound, spaceBound, meaning, model⟩ :=
    ForestZeroRootLoop.first_success_execution program actualQueries ready feasible witnessed resume dispatch work
      scratch (13 * channels) channels contract emptyReady emptyFits emptyAt actualQueries
      ⟨[], by simp [actualQueries]⟩ initial initialReady
  have workSum := ForestZeroRootLoop.linear_work_sum actualQueries work
    (fun position => queries[position].length) (fun position => queries[position].flatten.length)
    150 387 441 (by intro position inside; exact le_refl _)
  have rowSum : (actualQueries.map fun position => queries[position].length).sum = (queries.map List.length).sum := by
    change ((List.finRange queries.length).map fun position => queries[position].length).sum = _
    rw [← List.ofFn_eq_map]
    change (List.ofFn fun position : Fin queries.length => queries[position.val].length).sum = _
    exact congrArg List.sum (List.ofFn_getElem_eq_map queries List.length)
  have literalSum : (actualQueries.map fun position => queries[position].flatten.length).sum =
      (queries.map fun rows => rows.flatten.length).sum := by
    change ((List.finRange queries.length).map fun position => queries[position].flatten.length).sum = _
    rw [← List.ofFn_eq_map]
    change (List.ofFn fun position : Fin queries.length => queries[position.val].flatten.length).sum = _
    exact congrArg List.sum (List.ofFn_getElem_eq_map queries (fun rows => rows.flatten.length))
  have positionsLength : actualQueries.length = queries.length := by simp [actualQueries]
  rw [rowSum, literalSum, positionsLength] at workSum
  rw [positionsLength] at timeBound spaceBound
  refine ⟨answer, final, ticks, peak, trace, halted, decision, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · simpa only [actualQueries, List.mem_finRange, true_and] using meaning
  · simpa only [actualQueries, List.mem_finRange, true_and] using model

end Controller.Cost.ForestZeroAdmissibleCaller
