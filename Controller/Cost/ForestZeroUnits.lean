module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroAssembly
public import Controller.Cost.ForestZeroSource
public import Controller.Cost.ForestZeroInitialize

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! The fault-target control word is consumed from the serialized caller input
once and appended before dictionary reservation. Its channel ID is loaded from
that immutable cell for each forced-target unit. Metadata still reads the five
original packet headers; the fixed preparation constant six accounts for the
additional control cell. The finite clause and assignment bridges retain the
original root and channel identities. -/
namespace Controller.Cost.ForestZeroUnits
open Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Cost.GateProgram Controller.Cost.ForestZeroTouch
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroRows Controller.Cost.ForestZeroEmit
open Controller.Cost.ForestZeroSource Controller.Cost.ForestZeroAssembly
open Controller.Cost.ForestZeroInitialize (reserveHeap allocation_execution finish_execution loopCode finishCode)

/-- An extended packet has five metadata cells and one actual target trailer. -/
structure ControlHeader (heap : Array (Word width)) (channels nodes children guards roots : ℕ) : Prop where
  headerSize : 6 ≤ heap.size
  channelWord : heap[0]? = some (word width channels)
  nodeWord : heap[1]? = some (word width nodes)
  childWord : heap[2]? = some (word width children)
  guardWord : heap[3]? = some (word width guards)
  rootWord : heap[4]? = some (word width roots)
  packetLength : heap.size = 6 + 6 * nodes + children + guards + roots

def prepareCode (width : ℕ) : Code width :=
  [.constant 1 (word width 6), .add 1 0 1,
   .constant 0 (word width 0), .load 0 0,
   .constant 2 (word width 1), .load 2 2,
   .add 0 0 2, .add 2 1 0, .add 0 0 0]

def code (width base : ℕ) : Code width :=
  ForestInputMetadata.code width ++ prepareCode width ++ loopCode width (base + 25) ++ finishCode width

@[simp] theorem code_length : (code width base).length = 34 := rfl

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

private theorem put1_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 1 (word width value) =
      atState heap cursor x0 value x2 x3 stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

private theorem put2_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 2 (word width value) =
      atState heap cursor x0 x1 value x3 stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

theorem prepare_execution (program : Program width 4) (heap : Array (Word width))
    (channels nodes children guards roots : ℕ)
    (header : ControlHeader heap channels nodes children guards roots)
    (base second scratch2 scratch3 : ℕ) (stack output : List (Word width))
    (room : heap.size + 2 * (channels + nodes) < 2 ^ width)
    (programFits : base + 9 < 2 ^ width)
    (block : BlockAt program base (prepareCode width)) :
    Execution program
      (atState heap base (6 * nodes + children + guards + roots) second scratch2 scratch3 stack output)
      (atState heap (base + 9) (2 * (channels + nodes)) heap.size
        (heap.size + channels + nodes) scratch3 stack output)
      9 (5 + heap.size + stack.length + output.length) := by
  let payload := 6 * nodes + children + guards + roots
  let table := payload + 6
  let ambient := channels + nodes
  let inverse := table + ambient
  let s0 := atState heap base payload second scratch2 scratch3 stack output
  let s1 := atState heap (base + 1) payload 6 scratch2 scratch3 stack output
  let s2 := atState heap (base + 2) payload table scratch2 scratch3 stack output
  let s3 := atState heap (base + 3) 0 table scratch2 scratch3 stack output
  let s4 := atState heap (base + 4) channels table scratch2 scratch3 stack output
  let s5 := atState heap (base + 5) channels table 1 scratch3 stack output
  let s6 := atState heap (base + 6) channels table nodes scratch3 stack output
  let s7 := atState heap (base + 7) ambient table nodes scratch3 stack output
  let s8 := atState heap (base + 8) ambient table inverse scratch3 stack output
  let s9 := atState heap (base + 9) (2 * ambient) table inverse scratch3 stack output
  have packet := header.packetLength
  have headerSize := header.headerSize
  have tableEq : table = heap.size := by dsimp [table, payload]; omega
  have payloadWord : (word width payload).val = payload := Nat.mod_eq_of_lt (by dsimp [payload]; omega)
  have sixWord : (word width 6).val = 6 := Nat.mod_eq_of_lt (by omega)
  have tableWord : (word width table).val = table := Nat.mod_eq_of_lt (by rw [tableEq]; omega)
  have channelWord : (word width channels).val = channels := Nat.mod_eq_of_lt (by omega)
  have nodeWord : (word width nodes).val = nodes := Nat.mod_eq_of_lt (by omega)
  have ambientWord : (word width ambient).val = ambient := Nat.mod_eq_of_lt (by dsimp [ambient]; omega)
  have first : heap[0]'(by omega) = word width channels := by
    have entry := header.channelWord
    rw [Array.getElem?_eq_getElem (by omega)] at entry
    exact Option.some.inj entry
  have next : heap[1]'(by omega) = word width nodes := by
    have entry := header.nodeWord
    rw [Array.getElem?_eq_getElem (by omega)] at entry
    exact Option.some.inj entry
  have t0 : programStep program s0 = some s1 := by
    rw [fetched program s0 base (.constant 1 (word width 6)) rfl (by omega)
      (by simpa [prepareCode] using block 0 (by simp [prepareCode]))]
    change some (s0.advance.put 1 (word width 6)) = some s1
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put1_at]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.add 1 0 1) rfl (by omega)
      (by simpa [prepareCode] using block 1 (by simp [prepareCode]))]
    change some (s1.advance.put 1 (word width ((word width payload).val + (word width 6).val))) = some s2
    rw [payloadWord, sixWord, advance_at _ _ _ _ _ _ _ _ (by omega), put1_at]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (base + 2) (.constant 0 (word width 0)) rfl (by omega)
      (by simpa [prepareCode] using block 2 (by simp [prepareCode]))]
    change some (s2.advance.put 0 (word width 0)) = some s3
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (base + 3) (.load 0 0) rfl (by omega)
      (by simpa [prepareCode] using block 3 (by simp [prepareCode]))]
    change (if valid : (word width 0).val < heap.size then
      some (s3.advance.put 0 heap[(word width 0).val]) else none) = some s4
    rw [show (word width 0).val = 0 from Nat.zero_mod _, dite_eq_left (by omega), first,
      advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (base + 4) (.constant 2 (word width 1)) rfl (by omega)
      (by simpa [prepareCode] using block 4 (by simp [prepareCode]))]
    change some (s4.advance.put 2 (word width 1)) = some s5
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put2_at]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (base + 5) (.load 2 2) rfl (by omega)
      (by simpa [prepareCode] using block 5 (by simp [prepareCode]))]
    change (if valid : (word width 1).val < heap.size then
      some (s5.advance.put 2 heap[(word width 1).val]) else none) = some s6
    rw [show (word width 1).val = 1 from Nat.mod_eq_of_lt (by omega), dite_eq_left (by omega), next,
      advance_at _ _ _ _ _ _ _ _ (by omega), put2_at]
  have t6 : programStep program s6 = some s7 := by
    rw [fetched program s6 (base + 6) (.add 0 0 2) rfl (by omega)
      (by simpa [prepareCode] using block 6 (by simp [prepareCode]))]
    change some (s6.advance.put 0 (word width ((word width channels).val + (word width nodes).val))) = some s7
    rw [channelWord, nodeWord, advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have t7 : programStep program s7 = some s8 := by
    rw [fetched program s7 (base + 7) (.add 2 1 0) rfl (by omega)
      (by simpa [prepareCode] using block 7 (by simp [prepareCode]))]
    change some (s7.advance.put 2 (word width ((word width table).val + (word width ambient).val))) = some s8
    rw [tableWord, ambientWord, advance_at _ _ _ _ _ _ _ _ (by omega), put2_at]
  have t8 : programStep program s8 = some s9 := by
    rw [fetched program s8 (base + 8) (.add 0 0 0) rfl (by omega)
      (by simpa [prepareCode] using block 8 (by simp [prepareCode]))]
    change some (s8.advance.put 0 (word width ((word width ambient).val + (word width ambient).val))) = some s9
    rw [ambientWord, advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
    have double : ambient + ambient = 2 * ambient := by omega
    rw [double]
  have firstTrace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl s3)))
  have secondTrace := Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.refl s6)))
  have thirdTrace := Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.refl s9)))
  have joined := (firstTrace.append secondTrace).append thirdTrace
  have inverseEq : inverse = heap.size + channels + nodes := by dsimp [inverse, ambient]; rw [tableEq]; omega
  convert joined using 1 <;>
    simp only [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, payload, tableEq,
      inverseEq, ambient, atState_liveWords, Nat.max_self, Nat.zero_add] <;> omega

theorem initialize_execution (program : Program width 4) (heap : Array (Word width))
    (channels nodes children guards roots : ℕ)
    (header : ControlHeader heap channels nodes children guards roots)
    (base : ℕ) (stack output : List (Word width))
    (room : heap.size + 2 * (channels + nodes) < 2 ^ width)
    (programFits : base + 34 < 2 ^ width)
    (block : BlockAt program base (code width base)) :
    Execution program
      (atState heap base 0 0 0 0 stack output)
      (atState (reserveHeap heap (channels + nodes)) (base + 34)
        0 heap.size 0 0 (word width (heap.size + channels + nodes) :: stack) output)
      (28 + 14 * (channels + nodes))
      (6 + heap.size + 2 * (channels + nodes) + stack.length + output.length) := by
  let initial := atState heap base 0 0 0 0 stack output
  have allCode : BlockAt program base
      (ForestInputMetadata.code width ++
        (prepareCode width ++ (loopCode width (base + 25) ++ finishCode width))) := by
    simpa only [code, List.append_assoc] using block
  have metaBlock := BlockAt.prefix program base (ForestInputMetadata.code width)
    (prepareCode width ++ (loopCode width (base + 25) ++ finishCode width)) allCode
  have tailBlock := BlockAt.suffix program base (ForestInputMetadata.code width)
    (prepareCode width ++ (loopCode width (base + 25) ++ finishCode width)) allCode
  have prepareBlock : BlockAt program (base + 16) (prepareCode width) := by
    simpa only [ForestInputMetadata.code_length] using
      BlockAt.prefix program (base + (ForestInputMetadata.code width).length) (prepareCode width)
        (loopCode width (base + 25) ++ finishCode width) tailBlock
  have restBlock : BlockAt program (base + 25)
      (loopCode width (base + 25) ++ finishCode width) := by
    simpa only [ForestInputMetadata.code_length, prepareCode, List.length_cons,
      List.length_nil, Nat.add_assoc, Nat.reduceAdd] using
      BlockAt.suffix program (base + (ForestInputMetadata.code width).length) (prepareCode width)
        (loopCode width (base + 25) ++ finishCode width) tailBlock
  have loopBlock := BlockAt.prefix program (base + 25) (loopCode width (base + 25)) (finishCode width) restBlock
  have finishBlock : BlockAt program (base + 32) (finishCode width) := by
    simpa only [loopCode, List.length_cons, List.length_nil, Nat.add_assoc, Nat.reduceAdd] using
      BlockAt.suffix program (base + 25) (loopCode width (base + 25)) (finishCode width) restBlock
  have packet := header.packetLength
  have headerSize := header.headerSize
  have nodeStored : initial.heap[1]'(by simpa [initial, atState] using (show 1 < heap.size by omega)) = word width nodes := by
    have entry := header.nodeWord
    rw [Array.getElem?_eq_getElem (by omega)] at entry
    exact Option.some.inj entry
  have childStored : initial.heap[2]'(by simpa [initial, atState] using (show 2 < heap.size by omega)) = word width children := by
    have entry := header.childWord
    rw [Array.getElem?_eq_getElem (by omega)] at entry
    exact Option.some.inj entry
  have guardStored : initial.heap[3]'(by simpa [initial, atState] using (show 3 < heap.size by omega)) = word width guards := by
    have entry := header.guardWord
    rw [Array.getElem?_eq_getElem (by omega)] at entry
    exact Option.some.inj entry
  have rootStored : initial.heap[4]'(by simpa [initial, atState] using (show 4 < heap.size by omega)) = word width roots := by
    have entry := header.rootWord
    rw [Array.getElem?_eq_getElem (by omega)] at entry
    exact Option.some.inj entry
  have metadata := ForestInputMetadata.header_count_execution program initial base nodes children guards roots
    rfl rfl (by omega) (by omega)
    (by simpa only [initial, atState] using (show 5 ≤ heap.size by have := header.headerSize; omega)) nodeStored childStored guardStored rootStored metaBlock
  have metaState : ForestInputMetadata.scratchState initial (base + 16)
      (word width (6 * nodes + children + guards + roots)) (word width roots) =
      atState heap (base + 16) (6 * nodes + children + guards + roots) roots 0 0 stack output := by
    unfold ForestInputMetadata.scratchState initial atState
    congr 1
    funext register
    fin_cases register <;> rfl
  rw [metaState] at metadata
  have prepared := prepare_execution program heap channels nodes children guards roots header
    (base + 16) roots 0 0 stack output room (by omega) prepareBlock
  have allocated := allocation_execution program heap (base + 25) (2 * (channels + nodes))
    heap.size (heap.size + channels + nodes) 0 stack output (by omega) (by omega) (by omega) loopBlock
  simp only [ite_self] at allocated
  have finished := finish_execution program (reserveHeap heap (channels + nodes)) (base + 32)
    heap.size (heap.size + channels + nodes) stack output (by omega) finishBlock
  have joined := ((metadata.append prepared).append allocated).append finished
  convert joined using 1 <;>
    simp only [initial, atState_liveWords, reserveHeap, Array.size_append,
      Array.size_replicate, Nat.add_assoc, Nat.reduceAdd] <;> omega

/-- Three instructions consume the actual next serialized control word,
append it, and reset scratch. No target numeral occurs in the program. -/
def trailerCode (width : ℕ) : Code width := [.pop 3, .allocate 3, .constant 3 (word width 0)]

@[simp] theorem trailerCode_length : (trailerCode width).length = 3 := rfl

theorem trailer_execution (program : Program width 4) (heap : Array (Word width))
    (base x0 x1 x2 : ℕ) (target : Fin channels) (stack output : List (Word width))
    (programFits : base + 3 < 2 ^ width) (heapFits : heap.size < 2 ^ width)
    (block : BlockAt program base (trailerCode width)) :
    Execution program
      (atState heap base x0 x1 x2 0 (word width target.val :: stack) output)
      (atState (heap.push (word width target.val)) (base + 3) x0 x1 x2 0 stack output)
      3 (6 + heap.size + stack.length + output.length) := by
  let first := atState heap base x0 x1 x2 0 (word width target.val :: stack) output
  let loaded := atState heap (base + 1) x0 x1 x2 target.val stack output
  let appended := atState (heap.push (word width target.val)) (base + 2) x0 x1 x2 target.val stack output
  let final := atState (heap.push (word width target.val)) (base + 3) x0 x1 x2 0 stack output
  have t0 : programStep program first = some loaded := by
    rw [fetched program first base (.pop 3) rfl (by omega)
      (by simpa [trailerCode] using block 0 (by simp [trailerCode]))]
    change some { first.advance.put 3 (word width target.val) with stack := stack } = some loaded
    simp only [first, loaded, atState, State.advance, State.put,
      show (word width base).val = base from Nat.mod_eq_of_lt (by omega)]
    simp only [Option.some.injEq, State.mk.injEq, and_true, true_and]
    funext register
    fin_cases register <;> rfl
  have t1 : programStep program loaded = some appended := by
    rw [fetched program loaded (base + 1) (.allocate 3) rfl (by omega)
      (by simpa [trailerCode] using block 1 (by simp [trailerCode]))]
    simp only [step, loaded, appended, atState, State.advance, Bool.false_eq_true, ite_false,
      ite_true, heapFits, show (word width (base + 1)).val = base + 1 from Nat.mod_eq_of_lt (by omega),
      show (3 : Fin 4) ≠ 0 from by decide, show (3 : Fin 4) ≠ 1 from by decide,
      show (3 : Fin 4) ≠ 2 from by decide, Nat.add_assoc]
  have t2 : programStep program appended = some final := by
    rw [fetched program appended (base + 2) (.constant 3 (word width 0)) rfl (by omega)
      (by simpa [trailerCode] using block 2 (by simp [trailerCode]))]
    change some (appended.advance.put 3 (word width 0)) = some final
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  convert Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl final))) using 1 <;>
    simp only [first, loaded, appended, final, atState_liveWords, Array.size_push, List.length_cons] <;> omega

/-- The extended metadata contract is derived from the old loaded packet and
the actual allocation, rather than an enriched input supplied without cost. -/
private theorem pushed_prefix (heap : Array (Word width)) (value : Word width)
    (address : ℕ) (valid : address < heap.size) :
    (heap.push value)[address]? = heap[address]? := by
  simp only [Array.getElem?_push, ite_eq_right (show address ≠ heap.size by omega)]

theorem control_header {channels nodes children guards roots : ℕ} (heap : Array (Word width))
    (header : ForestZeroInitialize.PacketHeader heap channels nodes children guards roots)
    (target : Fin channels) :
    ControlHeader (heap.push (word width target.val)) channels nodes children guards roots := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Array.size_push]; have := header.headerSize; omega
  · exact (pushed_prefix heap (word width target.val) 0 (by have := header.headerSize; omega)).trans header.channelWord
  · exact (pushed_prefix heap (word width target.val) 1 (by have := header.headerSize; omega)).trans header.nodeWord
  · exact (pushed_prefix heap (word width target.val) 2 (by have := header.headerSize; omega)).trans header.childWord
  · exact (pushed_prefix heap (word width target.val) 3 (by have := header.headerSize; omega)).trans header.guardWord
  · exact (pushed_prefix heap (word width target.val) 4 (by have := header.headerSize; omega)).trans header.rootWord
  · rw [Array.size_push, header.packetLength]; omega

/-- Control loading and dictionary reservation share one fixed program. -/
def controlCode (width base : ℕ) : Code width := trailerCode width ++ code width (base + 3)

@[simp] theorem controlCode_length : (controlCode width base).length = 37 := rfl

theorem control_initialize_execution {channels nodes children guards roots : ℕ} (program : Program width 4) (heap : Array (Word width))
    (header : ForestZeroInitialize.PacketHeader heap channels nodes children guards roots)
    (target : Fin channels) (base : ℕ) (stack output : List (Word width))
    (room : heap.size + 1 + 2 * (channels + nodes) < 2 ^ width)
    (programFits : base + 37 < 2 ^ width)
    (block : BlockAt program base (controlCode width base)) :
    Execution program (atState heap base 0 0 0 0 (word width target.val :: stack) output)
      (atState (reserveHeap (heap.push (word width target.val)) (channels + nodes)) (base + 37)
        0 (heap.size + 1) 0 0 (word width (heap.size + 1 + channels + nodes) :: stack) output)
      (31 + 14 * (channels + nodes))
      (7 + heap.size + 2 * (channels + nodes) + stack.length + output.length) := by
  have prefixBlock := BlockAt.prefix program base _ _ block
  have initializationBlock : BlockAt program (base + 3) (code width (base + 3)) := by
    simpa only [trailerCode_length] using BlockAt.suffix program base _ _ block
  have loaded := trailer_execution program heap base 0 0 0 target stack output
    (by omega) (by omega) prefixBlock
  have initialized := initialize_execution program (heap.push (word width target.val))
    channels nodes children guards roots (control_header heap header target)
    (base + 3) stack output (by simpa only [Array.size_push] using room) (by omega) initializationBlock
  have peakEq : max (6 + heap.size + stack.length + output.length)
      (6 + (heap.size + 1) + 2 * (channels + nodes) + stack.length + output.length) =
      7 + heap.size + 2 * (channels + nodes) + stack.length + output.length := by
    rw [Nat.max_eq_right (by omega)]
    omega
  simp only [Nat.add_assoc] at peakEq
  convert loaded.append initialized using 1 <;>
    (try simp only [Array.size_push, Nat.add_assoc])
  all_goals first | omega | exact peakEq.symm

/-- Appending the physical control cell preserves every original source
occurrence while extending its immutable interval by exactly one cell. -/
theorem trailer_preserves_reference (heap : Array (Word width)) (channels : ℕ)
    (reference : Reference ambient)
    (stored : StoredReference heap channels heap.size reference) (targetWord : Word width) :
    StoredReference (heap.push targetWord) channels (heap.size + 1) reference := by
  refine ⟨by simp, by have := stored.slotBound; omega, by have := stored.headerBound; omega,
    ?_, ?_, stored.coordinateEq⟩
  · exact (pushed_prefix heap targetWord reference.slot stored.slotBound).trans stored.slotWord
  · exact (pushed_prefix heap targetWord 0 stored.headerBound).trans stored.channelWord

/-- The forced channel reference reads the new immutable trailer cell. -/
def targetReference (protectedEnd : ℕ) (target : Fin channels) : Reference (channels + nodes) :=
  channelReference (nodes := nodes) protectedEnd target true

theorem target_stored (heap : Array (Word width)) (channelsWord : heap[0]? = some (word width channels))
    (nonempty : 0 < heap.size) (target : Fin channels) :
    StoredReference (heap.push (word width target.val)) channels (heap.size + 1)
      (targetReference (nodes := nodes) heap.size target) := by
  refine ⟨by simp, by simp [targetReference, channelReference], by omega, ?_, ?_, ?_⟩
  · simp only [targetReference, channelReference, Array.getElem?_push, ite_true]
  · exact (pushed_prefix heap (word width target.val) 0 nonempty).trans channelsWord
  · simp only [targetReference, channelReference, Bool.false_eq_true, ite_false, Nat.add_zero]

/-- Shared reservation retains the actual control source cell and yields the
same first-touch representation as the existing once-only allocator. -/
theorem reserved_target_stored (heap : Array (Word width))
    (channelsWord : heap[0]? = some (word width channels)) (nonempty : 0 < heap.size)
    (target : Fin channels) :
    StoredReference (reserveHeap (heap.push (word width target.val)) (channels + nodes))
      channels (heap.size + 1) (targetReference (nodes := nodes) heap.size target) := by
  have original := target_stored (nodes := nodes) heap channelsWord nonempty target
  refine ⟨?_, original.slotBound, original.headerBound, ?_, ?_, original.coordinateEq⟩
  · rw [ForestZeroInitialize.reserveHeap_size, Array.size_push]; omega
  · exact (ForestZeroInitialize.reserve_source _ _ _ (by simp [targetReference, channelReference])).trans original.slotWord
  · exact (ForestZeroInitialize.reserve_source _ _ _ (by rw [Array.size_push]; omega)).trans original.channelWord

/-- The physical unit stream contains the declared root's negative
activity and the forced target's positive channel, in that order. -/
def forcedUnits (root : Reference (channels + nodes)) (protectedEnd : ℕ) (target : Fin channels) :
    List (Reference (channels + nodes)) := [{ root with positive := false }, targetReference protectedEnd target]

/-- This endpoint invokes the actual source-load/first-touch/two-allocation
emitter for both unit occurrences, preserving repeated references and the
shared inverse-base stack word. -/
theorem forced_units_execution (program : Program width 4) (heap : Array (Word width))
    (root : Reference (channels + nodes))
    (rootStored : StoredReference heap channels heap.size root)
    (target : Fin channels) (base input scratch : ℕ) (stack output : List (Word width))
    (room : heap.size + 1 + 2 * (channels + nodes) + 4 < 2 ^ width)
    (ambientFits : channels + nodes + 1 < 2 ^ width)
    (programFits : base + (emitCode width base (forcedUnits root heap.size target)).length < 2 ^ width)
    (block : BlockAt program base (emitCode width base (forcedUnits root heap.size target))) :
    let loadedHeap := heap.push (word width target.val)
    let initialHeap := reserveHeap loadedHeap (channels + nodes)
    let layout := ForestZeroInitialize.reservedLayout loadedHeap (channels + nodes)
    let references := forcedUnits root heap.size target
    let emitted := emitReferences initialHeap layout (empty (channels + nodes)) input scratch references
    ∃ ticks peak, Execution program
      (atState initialHeap base input layout.tableBase 0 scratch
        (word width layout.inverseBase :: stack) output)
      (atState emitted.heap (base + (emitCode width base references).length) emitted.input
        layout.tableBase emitted.dictionary.coordinates.size emitted.scratch
        (word width layout.inverseBase :: stack) output)
      ticks peak ∧ ticks ≤ 46 ∧
      peak ≤ 13 + heap.size + 2 * (channels + nodes) + stack.length + output.length := by
  let loadedHeap := heap.push (word width target.val)
  let initialHeap := reserveHeap loadedHeap (channels + nodes)
  let layout := ForestZeroInitialize.reservedLayout loadedHeap (channels + nodes)
  let references := forcedUnits root heap.size target
  have rootExtended := trailer_preserves_reference heap channels root rootStored (word width target.val)
  have rootReserved : StoredReference initialHeap channels (heap.size + 1) root := by
    refine ⟨?_, rootExtended.slotBound, rootExtended.headerBound, ?_, ?_, rootExtended.coordinateEq⟩
    · dsimp only [initialHeap, loadedHeap]; rw [ForestZeroInitialize.reserveHeap_size, Array.size_push]; omega
    · exact (ForestZeroInitialize.reserve_source loadedHeap (channels + nodes) root.slot
        (by simpa only [loadedHeap, Array.size_push] using rootExtended.slotBound)).trans rootExtended.slotWord
    · exact (ForestZeroInitialize.reserve_source loadedHeap (channels + nodes) 0
        (by simpa only [loadedHeap, Array.size_push] using rootExtended.headerBound)).trans rootExtended.channelWord
  have targetReserved := reserved_target_stored (nodes := nodes) heap rootStored.channelWord
    rootStored.headerBound target
  have stored : ∀ reference ∈ references, StoredReference initialHeap channels (heap.size + 1) reference := by
    intro reference member
    simp [references, forcedUnits] at member
    rcases member with rfl | rfl
    · exact ⟨rootReserved.sourceBound, rootReserved.slotBound, rootReserved.headerBound,
        rootReserved.slotWord, rootReserved.channelWord, rootReserved.coordinateEq⟩
    · exact targetReserved
  obtain ⟨ticks, peak, trace, tickBound, peakBound⟩ := emitReferences_execution program initialHeap layout
    (empty (channels + nodes)) (ForestZeroInitialize.reserve_represented loadedHeap (channels + nodes))
    channels (heap.size + 1) references stored
    (by simp only [layout, ForestZeroInitialize.reservedLayout, loadedHeap, Array.size_push]; omega)
    (by simp only [layout, ForestZeroInitialize.reservedLayout, loadedHeap, Array.size_push]; omega)
    base input scratch stack output
    (by simpa only [initialHeap, loadedHeap, ForestZeroInitialize.reserveHeap_size,
      Array.size_push, references, forcedUnits, List.length_cons, List.length_nil] using room)
    ambientFits programFits block
  refine ⟨ticks, peak, trace, ?_, ?_⟩
  · simpa only [references, forcedUnits, List.length_cons, List.length_nil] using tickBound
  · dsimp only [initialHeap, loadedHeap] at peakBound
    simp only [ForestZeroInitialize.reserveHeap_size, Array.size_push, references, forcedUnits,
      List.length_cons, List.length_nil] at peakBound
    omega

/-- The unit rows retain the declared root occurrence and actual target
trailer slot. Distinct root positions remain distinct even with equal IDs. -/
def forcedUnitRows (width : ℕ) (graph : DAG channels) (rows : List ForestIndexedOperands.Row)
    (roots : List ℕ) (position : Fin graph.roots.length) (target : Channel channels) :
    List (List (Reference (channels + graph.nodeCount))) :=
  [[rootReference graph rows roots position false],
    [targetReference (ForestZeroSource.packetHeap (width := width) channels rows roots).size target]]

def forcedUnitClauses (graph : DAG channels) (root : Fin graph.nodeCount) (target : Channel channels) :
    List (Clause graph.ZeroVar) := [[(.inr root, false)], [(.inl target, true)]]

theorem forcedUnitRows_original (graph : DAG channels) (rows : List ForestIndexedOperands.Row)
    (roots : List ℕ) (position : Fin graph.roots.length) (target : Channel channels) :
    originalRows (forcedUnitRows (width := width) graph rows roots position target) =
      (forcedUnitClauses graph (graph.roots.get position) target).map
        (List.map (fun literal => (sourceIndex graph literal.1, literal.2))) := by
  rfl

theorem forcedUnitClauses_holds (graph : DAG channels) (root : Fin graph.nodeCount)
    (target : Channel channels) (K : Finset (Channel channels))
    (activities : Fin graph.nodeCount → Bool) :
    (∀ clause ∈ forcedUnitClauses graph root target,
      ClauseHolds (graph.zeroAssignment (assignmentOfSet K) activities) clause) ↔
      activities root = false ∧ target ∈ K := by
  simp [forcedUnitClauses, ClauseHolds, LiteralHolds, DAG.zeroAssignment,
    assignmentOfSet_eq_true]

/-- Forced-target membership supplies nonemptiness. It does not require the
original global clause scanning every channel. -/
theorem forced_target_zero (graph : DAG channels) (guarded : graph.Guarded)
    (nodes : Finset (Fin graph.nodeCount)) (closed : graph.ChildClosed nodes)
    (root : Fin graph.nodeCount) (present : root ∈ nodes)
    (target : Channel channels) (K : Finset (Channel channels)) :
    (∃ activities, ForestZeroCone.LocalForward graph nodes (assignmentOfSet K) activities ∧
      activities root = false ∧ target ∈ K) ↔
      Admissible 1 target K ∧ graph.eval (assignmentOfSet K) root = false := by
  constructor
  · rintro ⟨activities, forward, zero, forced⟩
    exact ⟨⟨⟨target, forced⟩, fun _ => forced⟩,
      (ForestZeroCone.local_zero_iff graph guarded nodes closed K root present).mp
        ⟨activities, forward, zero⟩⟩
  · rintro ⟨eligible, zero⟩
    obtain ⟨activities, forward, rootZero⟩ :=
      (ForestZeroCone.local_zero_iff graph guarded nodes closed K root present).mpr zero
    exact ⟨activities, forward, rootZero, eligible.2 rfl⟩

end Controller.Cost.ForestZeroUnits
