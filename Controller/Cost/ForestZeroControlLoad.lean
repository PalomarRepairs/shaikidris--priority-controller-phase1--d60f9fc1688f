module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroUnits

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! The fixed cold entry loads the actual five-word graph header and payload,
clears the four scratch registers, consumes the serialized target word, and
reserves the shared dictionary once. All three phases execute the same fetched
program. The caller suffix and output remain in the storage bound. -/
namespace Controller.Cost.ForestZeroControlLoad
open Controller.Cost.GateProgram Controller.Cost.ForestZeroTouch
open Controller.Cost.ForestZeroInitialize

def clearCode (width : ℕ) : Code width :=
  [.constant 0 (word width 0), .constant 1 (word width 0),
   .constant 2 (word width 0), .constant 3 (word width 0)]

@[simp] theorem clearCode_length : (clearCode width).length = 4 := rfl

private theorem fetched (program : Program width 4) (state : State width 4)
    (cursor : ℕ) (instruction : Instruction width 4)
    (pc : state.pc = word width cursor) (fits : cursor < 2 ^ width)
    (entry : program[cursor]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [pc, show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits, entry]
  rfl

private theorem advance_pc (state : State width 4) (cursor : ℕ)
    (pc : state.pc = word width cursor) (fits : cursor < 2 ^ width) :
    state.advance.pc = word width (cursor + 1) := by
  simp only [State.advance, pc]
  rw [show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits]

/-- Clearing uses four actual constants, including the loader's unspecified
scratch registers. No zero-register premise is imposed on the loader endpoint. -/
theorem clear_execution (program : Program width 4) (state : State width 4)
    (base : ℕ) (pc : state.pc = word width base) (running : state.halted = false)
    (fits : base + 4 < 2 ^ width) (block : BlockAt program base (clearCode width)) :
    Execution program state (atState state.heap (base + 4) 0 0 0 0 state.stack state.output)
      4 state.liveWords := by
  let one := state.advance.put 0 (word width 0)
  let two := one.advance.put 1 (word width 0)
  let three := two.advance.put 2 (word width 0)
  let final := three.advance.put 3 (word width 0)
  have p1 : one.pc = word width (base + 1) := by
    simpa only [one, State.put] using advance_pc state base pc (by omega)
  have p2 : two.pc = word width (base + 2) := by
    simpa only [two, State.put, Nat.add_assoc] using advance_pc one (base + 1) p1 (by omega)
  have p3 : three.pc = word width (base + 3) := by
    simpa only [three, State.put, Nat.add_assoc] using advance_pc two (base + 2) p2 (by omega)
  have p4 : final.pc = word width (base + 4) := by
    simpa only [final, State.put, Nat.add_assoc] using advance_pc three (base + 3) p3 (by omega)
  have step0 : programStep program state = some one := by
    rw [fetched program state base (.constant 0 (word width 0)) pc (by omega)
      (by simpa only [clearCode, List.getElem?_cons_zero, Nat.add_zero] using block 0 (by simp [clearCode]))]
    simp only [step, running, Bool.false_eq_true, ite_false, one]
  have step1 : programStep program one = some two := by
    rw [fetched program one (base + 1) (.constant 1 (word width 0)) p1 (by omega)
      (by simpa [clearCode] using block 1 (by simp [clearCode]))]
    simp [step, one, two, State.put, State.advance, running]
  have step2 : programStep program two = some three := by
    rw [fetched program two (base + 2) (.constant 2 (word width 0)) p2 (by omega)
      (by simpa [clearCode] using block 2 (by simp [clearCode]))]
    simp [step, one, two, three, State.put, State.advance, running]
  have step3 : programStep program three = some final := by
    rw [fetched program three (base + 3) (.constant 3 (word width 0)) p3 (by omega)
      (by simpa [clearCode] using block 3 (by simp [clearCode]))]
    simp [step, one, two, three, final, State.put, State.advance, running]
  have live1 : one.liveWords = state.liveWords := rfl
  have live2 : two.liveWords = state.liveWords := rfl
  have live3 : three.liveWords = state.liveWords := rfl
  have live4 : final.liveWords = state.liveWords := rfl
  have first := Execution.cons step0 (Execution.cons step1 (Execution.refl two))
  have second := Execution.cons step2 (Execution.cons step3 (Execution.refl final))
  have trace : Execution program state final 4 state.liveWords := by
    simpa only [live1, live2, live3, live4, Nat.max_self] using first.append second
  have finalEq : final = atState state.heap (base + 4) 0 0 0 0 state.stack state.output := by
    unfold final three two one atState State.put State.advance
    simp only [State.mk.injEq, and_true, true_and]
    constructor
    · funext register; fin_cases register <;> rfl
    · constructor
      · simpa only [final, three, two, one, State.put, State.advance] using p4
      · exact running
  exact finalEq ▸ trace

/-- The cold entry contains 74 instructions, independent of graph size. -/
def code (width base : ℕ) : Code width :=
  ForestInputMetadata.fullCode width base ++ clearCode width ++
    ForestZeroUnits.controlCode width (base + 37)

@[simp] theorem code_length : (code width base).length = 74 := rfl

def packetHeap (width channels nodes children guards roots : ℕ)
    (payload : List (Word width)) : Array (Word width) :=
  (ForestInputMetadata.headerWords width channels nodes children guards roots).toArray ++ payload.toArray

/-- The metadata relation is derived from the loaded cells and payload length. -/
theorem packet_header (payload : List (Word width))
    (length_eq : payload.length = 6 * nodes + children + guards + roots) :
    PacketHeader (packetHeap width channels nodes children guards roots payload)
      channels nodes children guards roots := by
  have size : (packetHeap width channels nodes children guards roots payload).size = 5 + payload.length := by
    simp only [packetHeap, Array.size_append, List.size_toArray, ForestInputMetadata.headerWords, List.length_cons, List.length_nil] <;> omega
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [packetHeap, ForestInputMetadata.headerWords, length_eq] <;> omega

/-- Full fixed entry: the target is a consumed input word, dictionary zeroing
occurs once, and the physical inverse-base word is retained on the stack. -/
theorem execution (program : Program width 4) (base channels nodes children guards roots : ℕ)
    (payload stack output : List (Word width)) (target : Fin channels)
    (address loaded temporary : Word width)
    (length_eq : payload.length = 6 * nodes + children + guards + roots)
    (room : 6 + payload.length + 2 * (channels + nodes) < 2 ^ width)
    (fits : base + 74 < 2 ^ width) (block : BlockAt program base (code width base)) :
    Execution program
      ((ForestCounter.counterState (#[] : Array (Word width)) base address loaded temporary).frame
        (ForestInputMetadata.headerWords width channels nodes children guards roots ++ payload ++
          (word width target.val :: stack)) output)
      (atState (reserveHeap ((packetHeap width channels nodes children guards roots payload).push
        (word width target.val)) (channels + nodes)) (base + 74)
        0 (6 + payload.length) 0 0
        (word width (6 + payload.length + channels + nodes) :: stack) output)
      (62 + 7 * payload.length + 14 * (channels + nodes))
      (12 + payload.length + 2 * (channels + nodes) + stack.length + output.length) := by
  have whole : BlockAt program base (ForestInputMetadata.fullCode width base ++
      (clearCode width ++ ForestZeroUnits.controlCode width (base + 37))) := by
    simpa only [code, List.append_assoc] using block
  have loaderBlock : BlockAt program base (ForestInputMetadata.fullCode width base) :=
    BlockAt.prefix program base _ _ whole
  have remaining : BlockAt program (base + 33)
      (clearCode width ++ ForestZeroUnits.controlCode width (base + 37)) := by
    simpa only [ForestInputMetadata.fullCode_length] using
      BlockAt.suffix program base (ForestInputMetadata.fullCode width base) _ whole
  have clearBlock : BlockAt program (base + 33) (clearCode width) :=
    BlockAt.prefix program (base + 33) _ _ remaining
  have initBlock : BlockAt program (base + 37) (ForestZeroUnits.controlCode width (base + 37)) := by
    simpa only [clearCode_length, Nat.add_assoc] using
      BlockAt.suffix program (base + 33) (clearCode width) _ remaining
  obtain ⟨loadedState, loadedTrace, heapEq, stackEq, outputEq, pcEq, running⟩ :=
    ForestInputMetadata.cold_packet_execution program base channels nodes children guards roots payload
      (word width target.val :: stack) output address loaded temporary length_eq (by omega) (by omega) loaderBlock
  have heapEq' : loadedState.heap = packetHeap width channels nodes children guards roots payload := heapEq
  have cleared := clear_execution program loadedState (base + 33) pcEq running (by omega) clearBlock
  have initialized := ForestZeroUnits.control_initialize_execution program
    (packetHeap width channels nodes children guards roots payload) (packet_header payload length_eq)
    target (base + 37) stack output (by simp [packetHeap, ForestInputMetadata.headerWords, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]; omega)
    (by omega) initBlock
  have size : (packetHeap width channels nodes children guards roots payload).size = 5 + payload.length := by
    simp only [packetHeap, Array.size_append, List.size_toArray, ForestInputMetadata.headerWords, List.length_cons, List.length_nil] <;> omega
  have clearedEq : atState loadedState.heap (base + 33 + 4) 0 0 0 0 loadedState.stack loadedState.output =
      atState (packetHeap width channels nodes children guards roots payload) (base + 37)
        0 0 0 0 (word width target.val :: stack) output := by
    rw [heapEq', stackEq, outputEq]
  rw [clearedEq] at cleared
  have loadedLive : loadedState.liveWords = 11 + payload.length + stack.length + output.length := by
    simp only [State.liveWords, heapEq', stackEq, outputEq, List.length_cons]
    change 4 + (packetHeap width channels nodes children guards roots payload).size +
      (stack.length + 1) + output.length + 1 = _
    rw [size]; omega
  rw [loadedLive] at cleared
  have finishPC : base + 37 + 37 = base + 74 := by omega
  have finishBase : (packetHeap width channels nodes children guards roots payload).size + 1 =
      6 + payload.length := by rw [size]; omega
  rw [finishPC, finishBase] at initialized
  convert (loadedTrace.append cleared).append initialized using 1 <;>
    (try simp only [size, loadedLive, List.length_cons, Nat.add_assoc])
  all_goals omega

end Controller.Cost.ForestZeroControlLoad
