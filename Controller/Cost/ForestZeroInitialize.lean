module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroReset
public import Controller.Cost.ForestInputMetadata

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Once-only initialization reserves two ambient-sized zero regions after the
actual loaded source packet. The packet length and ambient dimension are formed
from stored header words. A fixed allocation loop avoids per-root initialization
and runtime-dependent instruction generation. -/
namespace Controller.Cost.ForestZeroInitialize
open Controller.Cost.ForestZeroCompile
open Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroTouch
open Controller.Cost.GateProgram

/-- Metadata16 first forms the payload length. These nine instructions form the
actual table base, read n and N, and form inverse base and allocation count. -/
def prepareCode (width : ℕ) : Code width :=
  [.constant 1 (word width 5), .add 1 0 1,
   .constant 0 (word width 0), .load 0 0,
   .constant 2 (word width 1), .load 2 2,
   .add 0 0 2, .add 2 1 0, .add 0 0 0]

def loopCode (width base : ℕ) : Code width :=
  [.branchZero 0 (word width (base + 7)),
   .constant 3 (word width 0), .allocate 3,
   .constant 3 (word width (2 ^ width - 1)), .add 0 0 3,
   .constant 3 (word width 0), .branchZero 3 (word width base)]

/-- The actual inverse-base word is retained on the caller stack; register two
is initialized to the empty local count rather than a supplied symbolic base. -/
def finishCode (width : ℕ) : Code width := [.push 2, .constant 2 (word width 0)]

def code (width base : ℕ) : Code width :=
  ForestInputMetadata.code width ++ prepareCode width ++ loopCode width (base + 25) ++ finishCode width

@[simp] theorem code_length : (code width base).length = 34 := rfl

/-- Header correspondence is with the exact loaded packet, not an arbitrary
heap whose size is treated as an available runtime register. -/
structure PacketHeader (heap : Array (Word width)) (channels nodes children guards roots : ℕ) : Prop where
  headerSize : 5 ≤ heap.size
  channelWord : heap[0]? = some (word width channels)
  nodeWord : heap[1]? = some (word width nodes)
  childWord : heap[2]? = some (word width children)
  guardWord : heap[3]? = some (word width guards)
  rootWord : heap[4]? = some (word width roots)
  packetLength : heap.size = 5 + 6 * nodes + children + guards + roots

/-- This array is the output specification of the once-only allocation loop. -/
def reserveHeap (heap : Array (Word width)) (ambient : ℕ) : Array (Word width) :=
  heap ++ Array.replicate (2 * ambient) (word width 0)

@[simp] theorem reserveHeap_size (heap : Array (Word width)) (ambient : ℕ) :
    (reserveHeap heap ambient).size = heap.size + 2 * ambient := by simp [reserveHeap]

def reservedLayout (heap : Array (Word width)) (ambient : ℕ) :
    Layout ambient (reserveHeap heap ambient).size where
  tableBase := heap.size
  inverseBase := heap.size + ambient
  tableBound := by simp only [reserveHeap_size]; omega
  inverseBound := by simp only [reserveHeap_size]; omega
  disjoint := Or.inl (Nat.le_refl _)

/-- Every original source cell is preserved by the once-only append. -/
theorem reserve_source (heap : Array (Word width)) (ambient address : ℕ)
    (bounded : address < heap.size) :
    (reserveHeap heap ambient)[address]? = heap[address]? := by
  exact Array.getElem?_append_left bounded

/-- Actual appended zeros represent the shared empty slot dictionary. The
inverse prefix is empty, so unused reserved inverse cells carry no stale IDs. -/
theorem reserve_represented (heap : Array (Word width)) (ambient : ℕ) :
    Represented (reserveHeap heap ambient) (reservedLayout heap ambient) (empty ambient) := by
  constructor
  · exact empty_coherent ambient
  · intro coordinate
    change (heap ++ Array.replicate (2 * ambient) (word width 0))[heap.size + coordinate.val]? =
      some (word width (empty ambient).slots[coordinate.val])
    rw [Array.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left, Array.getElem?_replicate, empty,
      Vector.getElem_replicate]
    rw [ite_eq_left (by have := coordinate.isLt; omega)]
  · intro index coordinate present
    simp only [empty, Array.getElem?_empty] at present
    contradiction

/-- Packet framing derives the physical table and inverse bases from the five
actual metadata words that the fixed prepare phase reads. -/
theorem header_layout_bases (heap : Array (Word width)) (channels nodes children guards roots : ℕ)
    (header : PacketHeader heap channels nodes children guards roots) :
    (reservedLayout heap (channels + nodes)).tableBase = 5 + 6 * nodes + children + guards + roots ∧
    (reservedLayout heap (channels + nodes)).inverseBase =
      5 + 6 * nodes + children + guards + roots + channels + nodes := by
  simp [reservedLayout, header.packetLength, Nat.add_assoc]

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

/-- A nonempty initialization iteration performs one real allocation and
returns to the fixed loop head. The two derived region bases are retained. -/
theorem allocation_iteration (program : Program width 4) (heap : Array (Word width))
    (base count tableBase inverseBase scratch : ℕ) (stack output : List (Word width))
    (countFits : count + 1 < 2 ^ width) (heapFits : heap.size < 2 ^ width)
    (programFits : base + 7 < 2 ^ width)
    (block : BlockAt program base (loopCode width base)) :
    Execution program
      (atState heap base (count + 1) tableBase inverseBase scratch stack output)
      (atState (heap.push (word width 0)) base count tableBase inverseBase 0 stack output)
      7 (6 + heap.size + stack.length + output.length) := by
  let nextHeap := heap.push (word width 0)
  let s0 := atState heap base (count + 1) tableBase inverseBase scratch stack output
  let s1 := atState heap (base + 1) (count + 1) tableBase inverseBase scratch stack output
  let s2 := atState heap (base + 2) (count + 1) tableBase inverseBase 0 stack output
  let s3 := atState nextHeap (base + 3) (count + 1) tableBase inverseBase 0 stack output
  let s4 := atState nextHeap (base + 4) (count + 1) tableBase inverseBase (2 ^ width - 1) stack output
  let s5 := atState nextHeap (base + 5) count tableBase inverseBase (2 ^ width - 1) stack output
  let s6 := atState nextHeap (base + 6) count tableBase inverseBase 0 stack output
  let s7 := atState nextHeap base count tableBase inverseBase 0 stack output
  have countWord : (word width (count + 1)).val = count + 1 := Nat.mod_eq_of_lt countFits
  have maximumFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have maximumWord : (word width (2 ^ width - 1)).val = 2 ^ width - 1 := Nat.mod_eq_of_lt maximumFits
  have decoded : word width ((count + 1) + (2 ^ width - 1)) = word width count := by
    have same : (count + 1) + (2 ^ width - 1) = count + 2 ^ width := by have := Nat.two_pow_pos width; omega
    apply Fin.ext
    simp only [word, same, Nat.add_mod_right]
  have t0 : programStep program s0 = some s1 := by
    rw [fetched program s0 base (.branchZero 0 (word width (base + 7))) rfl (by omega)
      (by simpa [loopCode] using block 0 (by simp [loopCode]))]
    change some (if (word width (count + 1)).val = 0 then
      { s0.advance with pc := word width (base + 7) } else s0.advance) = some s1
    rw [countWord, ite_eq_right (by omega), advance_at _ _ _ _ _ _ _ _ (by omega)]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.constant 3 (word width 0)) rfl (by omega)
      (by simpa [loopCode] using block 1 (by simp [loopCode]))]
    change some (s1.advance.put 3 (word width 0)) = some s2
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (base + 2) (.allocate 3) rfl (by omega)
      (by simpa [loopCode] using block 2 (by simp [loopCode]))]
    change (if heap.size < 2 ^ width then
      some { s2.advance with heap := heap.push (word width 0) } else none) = some s3
    rw [ite_eq_left heapFits, advance_at _ _ _ _ _ _ _ _ (by omega)] <;> rfl
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (base + 3) (.constant 3 (word width (2 ^ width - 1))) rfl (by omega)
      (by simpa [loopCode] using block 3 (by simp [loopCode]))]
    change some (s3.advance.put 3 (word width (2 ^ width - 1))) = some s4
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (base + 4) (.add 0 0 3) rfl (by omega)
      (by simpa [loopCode] using block 4 (by simp [loopCode]))]
    change some (s4.advance.put 0 (word width ((word width (count + 1)).val +
      (word width (2 ^ width - 1)).val))) = some s5
    rw [countWord, maximumWord, decoded, advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (base + 5) (.constant 3 (word width 0)) rfl (by omega)
      (by simpa [loopCode] using block 5 (by simp [loopCode]))]
    change some (s5.advance.put 3 (word width 0)) = some s6
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t6 : programStep program s6 = some s7 := by
    rw [fetched program s6 (base + 6) (.branchZero 3 (word width base)) rfl (by omega)
      (by simpa [loopCode] using block 6 (by simp [loopCode]))]
    change some (if (word width 0).val = 0 then { s6.advance with pc := word width base }
      else s6.advance) = some s7
    simp only [word, Nat.zero_mod, ite_true]
    rw [advance_at _ _ _ _ _ _ _ _ (by omega)] <;> rfl
  have first := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl s3)))
  have second := Execution.cons t3 (Execution.cons t4 (Execution.refl s5))
  have third := Execution.cons t5 (Execution.cons t6 (Execution.refl s7))
  have joined := (first.append second).append third
  convert joined using 1 <;>
    simp only [s0, s1, s2, s3, s4, s5, s6, s7, nextHeap, atState_liveWords,
      Array.size_push, Nat.max_self, Nat.zero_add] <;> omega

/-- The complete fixed allocation loop appends exactly its runtime count of
zero words, preserving the original heap prefix and caller frames. -/
theorem allocation_execution (program : Program width 4) (heap : Array (Word width))
    (base count tableBase inverseBase scratch : ℕ) (stack output : List (Word width))
    (countFits : count < 2 ^ width) (room : heap.size + count ≤ 2 ^ width)
    (programFits : base + 7 < 2 ^ width)
    (block : BlockAt program base (loopCode width base)) :
    Execution program
      (atState heap base count tableBase inverseBase scratch stack output)
      (atState (heap ++ Array.replicate count (word width 0)) (base + 7)
        0 tableBase inverseBase (if count = 0 then scratch else 0) stack output)
      (7 * count + 1) (5 + heap.size + count + stack.length + output.length) := by
  induction count generalizing heap scratch with
  | zero =>
      let initial := atState heap base 0 tableBase inverseBase scratch stack output
      let final := atState heap (base + 7) 0 tableBase inverseBase scratch stack output
      have transition : programStep program initial = some final := by
        rw [fetched program initial base (.branchZero 0 (word width (base + 7))) rfl (by omega)
          (by simpa [loopCode] using block 0 (by simp [loopCode]))]
        change some (if (word width 0).val = 0 then
          { initial.advance with pc := word width (base + 7) } else initial.advance) = some final
        simp only [word, Nat.zero_mod, ite_true]
        rw [advance_at _ _ _ _ _ _ _ _ (by omega)] <;> rfl
      have actual := Execution.cons transition (Execution.refl final)
      simpa [initial, final] using actual
  | succ count ih =>
      have first := allocation_iteration program heap base count tableBase inverseBase scratch
        stack output countFits (by omega) programFits block
      have rest := ih (heap.push (word width 0)) 0 (by omega) (by simp only [Array.size_push]; omega)
      have joined := first.append rest
      convert joined using 1
      · simp only [Array.replicate_succ', Array.push_eq_append, Array.append_assoc,
          ite_eq_right (show count + 1 ≠ 0 by omega), ite_self]
      · omega
      · simp only [Array.size_push]
        omega

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

/-- The fixed preparation reads the two actual source dimension words and
forms both physical bases and twice the ambient size in machine registers. -/
theorem prepare_execution (program : Program width 4) (heap : Array (Word width))
    (channels nodes children guards roots : ℕ)
    (header : PacketHeader heap channels nodes children guards roots)
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
  let table := payload + 5
  let ambient := channels + nodes
  let inverse := table + ambient
  let s0 := atState heap base payload second scratch2 scratch3 stack output
  let s1 := atState heap (base + 1) payload 5 scratch2 scratch3 stack output
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
  have fiveWord : (word width 5).val = 5 := Nat.mod_eq_of_lt (by omega)
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
    rw [fetched program s0 base (.constant 1 (word width 5)) rfl (by omega)
      (by simpa [prepareCode] using block 0 (by simp [prepareCode]))]
    change some (s0.advance.put 1 (word width 5)) = some s1
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put1_at]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.add 1 0 1) rfl (by omega)
      (by simpa [prepareCode] using block 1 (by simp [prepareCode]))]
    change some (s1.advance.put 1 (word width ((word width payload).val + (word width 5).val))) = some s2
    rw [payloadWord, fiveWord, advance_at _ _ _ _ _ _ _ _ (by omega), put1_at]
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

/-- The final two fetched instructions retain the actual inverse-base word and
establish the empty local count in register two. -/
theorem finish_execution (program : Program width 4) (heap : Array (Word width))
    (base tableBase inverseBase : ℕ) (stack output : List (Word width))
    (programFits : base + 2 < 2 ^ width) (block : BlockAt program base (finishCode width)) :
    Execution program
      (atState heap base 0 tableBase inverseBase 0 stack output)
      (atState heap (base + 2) 0 tableBase 0 0 (word width inverseBase :: stack) output)
      2 (6 + heap.size + stack.length + output.length) := by
  let initial := atState heap base 0 tableBase inverseBase 0 stack output
  let middle := atState heap (base + 1) 0 tableBase inverseBase 0 (word width inverseBase :: stack) output
  let final := atState heap (base + 2) 0 tableBase 0 0 (word width inverseBase :: stack) output
  have first : programStep program initial = some middle := by
    rw [fetched program initial base (.push 2) rfl (by omega)
      (by simpa [finishCode] using block 0 (by simp [finishCode]))]
    change some { initial.advance with stack := word width inverseBase :: stack } = some middle
    rw [advance_at _ _ _ _ _ _ _ _ (by omega)] <;> rfl
  have last : programStep program middle = some final := by
    rw [fetched program middle (base + 1) (.constant 2 (word width 0)) rfl (by omega)
      (by simpa [finishCode] using block 1 (by simp [finishCode]))]
    change some (middle.advance.put 2 (word width 0)) = some final
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put2_at]
  have joined := Execution.cons first (Execution.cons last (Execution.refl final))
  convert joined using 1 <;>
    simp only [initial, middle, final, atState_liveWords, List.length_cons, Nat.zero_add] <;> omega

/-- Complete once-only source-derived physical setup: metadata reads, dimension
reads/arithmetic, the fixed allocation loop, and real inverse-base retention.
Both zero regions are allocated once and the exact source prefix is preserved. -/
theorem initialize_execution (program : Program width 4) (heap : Array (Word width))
    (channels nodes children guards roots : ℕ)
    (header : PacketHeader heap channels nodes children guards roots)
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
    rfl rfl (by omega) (by omega) headerSize nodeStored childStored guardStored rootStored metaBlock
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

end Controller.Cost.ForestZeroInitialize
