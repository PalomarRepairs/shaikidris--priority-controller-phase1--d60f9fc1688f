module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestCursorAllRoots
public import Controller.Cost.InputLoad
public import Controller.Cost.SourceGateFieldFormation

@[expose] public section

/-!
# Stored forest source-address directory

Each indexed source row supplies two base addresses. The directory constructor
allocates their actual words once, and a four-instruction indexed read doubles
the supplied node index, adds the stored directory offset and loads its cell.
This is a physical address-lookup contract. Deriving the indexed input rows from
a decoder representation and forming the remaining compiler operands have
separate contracts.
-/
namespace Controller.Cost.ForestGraphDirectory
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestCounter Controller.Cost.ForestCursorTraversal
open Controller.Cost.ForestCursorMaterialize

structure Entry where
  childBase : ℕ
  guardBase : ℕ
  deriving DecidableEq, Repr

def values : List Entry → List ℕ
  | [] => []
  | entry :: rest => entry.childBase :: entry.guardBase :: values rest

@[simp] theorem values_length (entries : List Entry) :
    (values entries).length = 2 * entries.length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => simp [values, ih]; omega

theorem values_child (entries : List Entry) (index : ℕ) (valid : index < entries.length) :
    (values entries)[2 * index]'(by rw [values_length]; omega) = (entries[index]'valid).childBase := by
  induction entries generalizing index with
  | nil => simp at valid
  | cons entry rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          have next : index < rest.length := by simpa using valid
          simpa only [values, Nat.mul_succ, List.getElem_cons_succ] using ih index next

theorem values_guard (entries : List Entry) (index : ℕ) (valid : index < entries.length) :
    (values entries)[2 * index + 1]'(by rw [values_length]; omega) = (entries[index]'valid).guardBase := by
  induction entries generalizing index with
  | nil => simp at valid
  | cons entry rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          have next : index < rest.length := by simpa using valid
          simpa only [values, Nat.mul_succ, List.getElem_cons_succ] using ih index next

/-- The source rows are indexed data; no address function is evaluated by lookup. -/
structure Source (graph : DAG n) where
  entries : List Entry
  length_eq : entries.length = graph.nodeCount

def Source.entry (source : Source graph) (node : Fin graph.nodeCount) : Entry :=
  source.entries[node.val]'(by rw [source.length_eq]; exact node.isLt)

def Source.Matches (source : Source graph) (records : GraphRecords width heap graph) : Prop :=
  ∀ node, (source.entry node).childBase = records.childBase node ∧
    (source.entry node).guardBase = records.guardBase node

def backingHeap (width : ℕ) (heap : Array (Word width)) (entries : List Entry) :=
  allocatedHeap width heap (values entries)

def allocationCode (width : ℕ) (entries : List Entry) := writeCode width (values entries)

@[simp] theorem allocationCode_length (entries : List Entry) :
    (allocationCode width entries).length = 4 * entries.length := by
  simp [allocationCode]; omega

@[simp] theorem backingHeap_size (heap : Array (Word width)) (entries : List Entry) :
    (backingHeap width heap entries).size = heap.size + 2 * entries.length := by
  simp [backingHeap]

theorem child_word (heap : Array (Word width)) (entries : List Entry)
    (index : ℕ) (valid : index < entries.length) :
    (backingHeap width heap entries)[heap.size + 2 * index]'(by simp; omega) =
      word width (entries[index]'valid).childBase := by
  simpa only [backingHeap, values_child entries index valid] using
    allocatedHeap_cell width heap (values entries) (2 * index) (by rw [values_length]; omega)

theorem guard_word (heap : Array (Word width)) (entries : List Entry)
    (index : ℕ) (valid : index < entries.length) :
    (backingHeap width heap entries)[heap.size + 2 * index + 1]'(by simp; omega) =
      word width (entries[index]'valid).guardBase := by
  simpa only [backingHeap, Nat.add_assoc, values_guard entries index valid] using
    allocatedHeap_cell width heap (values entries) (2 * index + 1) (by rw [values_length]; omega)

/-- A fitted stored child base decodes to the exact natural source address. -/
theorem child_decodes (heap : Array (Word width)) (entries : List Entry)
    (index : ℕ) (valid : index < entries.length)
    (fits : (entries[index]'valid).childBase < 2 ^ width) :
    ((backingHeap width heap entries)[heap.size + 2 * index]'(by simp; omega)).val =
      (entries[index]'valid).childBase := by
  rw [child_word heap entries index valid]
  exact Nat.mod_eq_of_lt fits

/-- Guard and child bases have separate cells and representability premises. -/
theorem guard_decodes (heap : Array (Word width)) (entries : List Entry)
    (index : ℕ) (valid : index < entries.length)
    (fits : (entries[index]'valid).guardBase < 2 ^ width) :
    ((backingHeap width heap entries)[heap.size + 2 * index + 1]'(by simp; omega)).val =
      (entries[index]'valid).guardBase := by
  rw [guard_word heap entries index valid]
  exact Nat.mod_eq_of_lt fits

/-- All directory fields are allocated by fetched instructions exactly once. -/
theorem allocation_execution (machine : Program width 4) (heap : Array (Word width))
    (entries : List Entry) (base : ℕ) (address loaded temporary : Word width)
    (fits : base + 4 * entries.length < 2 ^ width)
    (room : heap.size + 2 * entries.length ≤ 2 ^ width)
    (block : BlockAt machine base (allocationCode width entries)) :
    ∃ finalTemporary, Execution machine (counterState heap base address loaded temporary)
      (counterState (backingHeap width heap entries) (base + 4 * entries.length)
        address loaded finalTemporary) (4 * entries.length) (5 + heap.size + 2 * entries.length) := by
  simpa only [values_length, backingHeap, ← Nat.mul_assoc, Nat.reduceMul] using
    write_execution machine heap base (values entries) address loaded temporary
      (by rw [values_length]; omega) (by rw [values_length]; exact room) block

/-- The input register is a node index, not a precomputed cell address. -/
def indexedCode (width offset : ℕ) : ForestCounter.Code width :=
  [.add 0 0 0, .constant 2 (word width offset), .add 0 0 2, .load 1 0]

@[simp] theorem indexedCode_length : (indexedCode width offset).length = 4 := rfl

private theorem state_advance (heap : Array (Word width)) (base : ℕ)
    (address loaded temporary : Word width) (fits : base < 2 ^ width) :
    (counterState heap base address loaded temporary).advance =
      counterState heap (base + 1) address loaded temporary := by
  unfold State.advance counterState
  rw [show (word width base).val = base from Nat.mod_eq_of_lt fits]

private theorem put_address (heap : Array (Word width)) (base : ℕ)
    (address loaded temporary next : Word width) :
    (counterState heap base address loaded temporary).put 0 next =
      counterState heap base next loaded temporary := by
  unfold State.put counterState
  congr 1
  funext register
  by_cases first : register = 0 <;> simp [first]

private theorem double_transition (machine : Program width 4) (heap : Array (Word width))
    (base : ℕ) (address loaded temporary : Word width) (fits : base < 2 ^ width)
    (fetched : machine[base]? = some (.add 0 0 0)) :
    programStep machine (counterState heap base address loaded temporary) =
      some (counterState heap (base + 1) (word width (address.val + address.val)) loaded temporary) := by
  unfold programStep
  rw [show (counterState heap base address loaded temporary).pc.val = base from Nat.mod_eq_of_lt fits, fetched]
  change step (.add (0 : Fin 4) 0 0) (counterState heap base address loaded temporary) = _
  simp only [step, counterState, Bool.false_eq_true, ite_false]
  change some ((counterState heap base address loaded temporary).advance.put 0
    (word width (address.val + address.val))) = _
  rw [state_advance _ _ _ _ _ fits, put_address]
  rfl

private theorem offset_transition (machine : Program width 4) (heap : Array (Word width))
    (base : ℕ) (address loaded temporary : Word width) (fits : base < 2 ^ width)
    (fetched : machine[base]? = some (.add 0 0 2)) :
    programStep machine (counterState heap base address loaded temporary) =
      some (counterState heap (base + 1) (word width (address.val + temporary.val)) loaded temporary) := by
  unfold programStep
  rw [show (counterState heap base address loaded temporary).pc.val = base from Nat.mod_eq_of_lt fits, fetched]
  change step (.add (0 : Fin 4) 0 2) (counterState heap base address loaded temporary) = _
  simp only [step, counterState, Bool.false_eq_true, ite_false]
  change some ((counterState heap base address loaded temporary).advance.put 0
    (word width (address.val + temporary.val))) = _
  rw [state_advance _ _ _ _ _ fits, put_address]
  rfl

/-- Four real instructions compute the indexed directory address and read it. -/
theorem indexed_execution (machine : Program width 4) (heap : Array (Word width))
    (base offset index : ℕ) (loaded temporary value : Word width)
    (fits : base + 4 < 2 ^ width) (addressFits : offset + 2 * index < 2 ^ width)
    (valid : offset + 2 * index < heap.size) (stored : heap[offset + 2 * index] = value)
    (block : BlockAt machine base (indexedCode width offset)) :
    Execution machine (counterState heap base (word width index) loaded temporary)
      (counterState heap (base + 4) (word width (offset + 2 * index)) value (word width offset))
      4 (5 + heap.size) := by
  have indexFits : index < 2 ^ width := by omega
  have doubledFits : 2 * index < 2 ^ width := by omega
  have offsetFits : offset < 2 ^ width := by omega
  have doubled : word width ((word width index).val + (word width index).val) = word width (2 * index) := by
    rw [show (word width index).val = index from Nat.mod_eq_of_lt indexFits]
    congr 1; omega
  have combined : word width ((word width (2 * index)).val + (word width offset).val) =
      word width (offset + 2 * index) := by
    rw [show (word width (2 * index)).val = 2 * index from Nat.mod_eq_of_lt doubledFits,
      show (word width offset).val = offset from Nat.mod_eq_of_lt offsetFits]
    congr 1; omega
  have first := double_transition machine heap base (word width index) loaded temporary (by omega)
    (by simpa [indexedCode] using block 0 (by simp [indexedCode]))
  rw [doubled] at first
  have second := increment_transition machine heap (base + 1) offset (word width (2 * index)) loaded temporary
    (by omega) (by simpa [indexedCode] using block 1 (by simp [indexedCode]))
  have third := offset_transition machine heap (base + 2) (word width (2 * index)) loaded (word width offset)
    (by omega) (by simpa [indexedCode] using block 2 (by simp [indexedCode]))
  rw [combined] at third
  have fourth := read_transition machine heap (base + 3) (offset + 2 * index) loaded (word width offset) value
    (by omega) addressFits valid stored
    (by simpa [indexedCode] using block 3 (by simp [indexedCode]))
  have trace := Execution.cons first (Execution.cons second (Execution.cons third
    (Execution.cons fourth (Execution.refl (counterState heap (base + 4)
      (word width (offset + 2 * index)) value (word width offset))))))
  simpa only [counterState_liveWords, Nat.add_assoc, Nat.zero_add, max_self] using trace

/-- Input words are transferred from the supplied stack into real directory
cells; their input storage is included in the initial live-word count. -/
theorem input_execution (machine : Program width 4) (state : State width 4)
    (entries : List Entry) (suffix : List (Word width)) (base : ℕ)
    (pc : state.pc = word width base) (running : state.halted = false)
    (input : state.stack = (values entries).map (word width) ++ suffix)
    (fits : base + 4 * entries.length < 2 ^ width)
    (room : state.heap.size + 2 * entries.length ≤ 2 ^ width)
    (block : BlockAt machine base (InputLoad.code (width := width) (2 * entries.length))) :
    ∃ final, Execution machine state final (4 * entries.length) state.liveWords ∧
      final.heap = backingHeap width state.heap entries ∧ final.stack = suffix ∧
      final.output = state.output ∧ final.pc = word width (base + 4 * entries.length) ∧
      final.halted = false := by
  have length : ((values entries).map (word width)).length = 2 * entries.length := by simp
  obtain ⟨final, trace, heap, stack, output, position, active⟩ :=
    InputLoad.code_execution machine state ((values entries).map (word width)) suffix base pc running input
      (by rw [length]; omega) (by rw [length]; exact room) (by simpa only [length] using block)
  refine ⟨final, ?_, heap, stack, output, ?_, active⟩
  · simpa only [length, ← Nat.mul_assoc, Nat.reduceMul] using trace
  · simpa only [length, ← Nat.mul_assoc, Nat.reduceMul] using position

/-- Register zero contains the computed directory cell address. One add copies
it into the source-address register; no address constant is reconstructed. -/
private theorem copy_source_execution (machine : Program width 4) (heap : Array (Word width))
    (base address : ℕ) (loaded temporary : Word width)
    (fits : base + 1 < 2 ^ width) (addressFits : address < 2 ^ width)
    (fetched : machine[base]? = some (.add 3 0 3)) :
    ∃ ready, Execution machine (counterState heap base (word width address) loaded temporary)
      ready 1 (5 + heap.size) ∧ ready.reg 3 = word width address ∧
      ready.heap = heap ∧ ready.stack = [] ∧ ready.output = [] ∧
      ready.pc = word width (base + 1) ∧ ready.halted = false := by
  let initial := counterState heap base (word width address) loaded temporary
  let ready := initial.advance.put 3 (word width address)
  have first : programStep machine initial = some ready := by
    unfold programStep
    rw [show initial.pc.val = base from Nat.mod_eq_of_lt (by omega), fetched]
    simp [step, initial, counterState, ready, word, Nat.mod_eq_of_lt addressFits]
  have next : ready.pc = word width (base + 1) := by
    change word width ((word width base).val + 1) = word width (base + 1)
    rw [show (word width base).val = base from Nat.mod_eq_of_lt (by omega)]
  have live : ready.liveWords = 5 + heap.size := by
    simp [ready, initial, State.liveWords, State.put, State.advance, counterState]
    omega
  refine ⟨ready, ?_, ?_, rfl, rfl, rfl, next, rfl⟩
  · have trace := Execution.cons first (Execution.refl ready)
    simpa only [initial, counterState_liveWords, live, Nat.zero_add, max_self] using trace
  · simp [ready, State.put]

/-- A uniform kernel reads an indexed source base, then forms and stores the
exact encoded constant instruction. Its code does not contain the source value. -/
def baseConstantCode (width offset : ℕ) : ForestCounter.Code width :=
  indexedCode width offset ++ [.add 3 0 3] ++ SourceGateFieldFormation.code width

@[simp] theorem baseConstantCode_length : (baseConstantCode width offset).length = 13 := by
  simp [baseConstantCode]

/-- Thirteen fetched transitions include address formation, both source reads,
field construction and four physical instruction-word allocations. -/
theorem baseConstant_execution (machine : Program width 4) (heap : Array (Word width))
    (base offset index value : ℕ) (loaded temporary : Word width)
    (fits : base + 13 < 2 ^ width) (addressFits : offset + 2 * index < 2 ^ width)
    (valueFits : value < 2 ^ width) (valid : offset + 2 * index < heap.size)
    (stored : heap[offset + 2 * index] = word width value)
    (room : heap.size + 4 ≤ 2 ^ width)
    (block : BlockAt machine base (baseConstantCode width offset)) :
    ∃ final, Execution machine (counterState heap base (word width index) loaded temporary)
      final 13 (9 + heap.size) ∧
      final.heap = heap ++ (InstructionEncoding.encode (.constant 0 (word width value) : Instruction width 4)).toArray ∧
      final.stack = [] ∧ final.output = [] ∧ final.pc = word width (base + 13) ∧ final.halted = false := by
  have splitBlock : BlockAt machine base
      (indexedCode width offset ++ ([.add 3 0 3] ++ SourceGateFieldFormation.code width)) := by
    simpa only [baseConstantCode, List.append_assoc] using block
  have firstBlock : BlockAt machine base (indexedCode width offset) := by
    exact BlockAt.prefix machine base (indexedCode width offset)
      ([.add 3 0 3] ++ SourceGateFieldFormation.code width) splitBlock
  have tailBlock : BlockAt machine (base + 4) ([.add 3 0 3] ++ SourceGateFieldFormation.code width) := by
    simpa only [indexedCode_length] using BlockAt.suffix machine base (indexedCode width offset)
      ([.add 3 0 3] ++ SourceGateFieldFormation.code width) splitBlock
  have copiedInstruction : machine[base + 4]? = some (.add 3 0 3) := by
    simpa using (BlockAt.prefix machine (base + 4) [.add 3 0 3] (SourceGateFieldFormation.code width) tailBlock) 0 (by simp)
  have sourceBlock : BlockAt machine (base + 5) (SourceGateFieldFormation.code width) := by
    simpa using BlockAt.suffix machine (base + 4) [.add 3 0 3] (SourceGateFieldFormation.code width) tailBlock
  have first := indexed_execution machine heap base offset index loaded temporary (word width value)
    (by omega) addressFits valid stored firstBlock
  obtain ⟨ready, copied, address, readyHeap, readyStack, readyOutput, readyPC, readyActive⟩ :=
    copy_source_execution machine heap (base + 4) (offset + 2 * index) (word width value) (word width offset)
      (by omega) addressFits copiedInstruction
  let channel : Channel (2 ^ width) := ⟨value, valueFits⟩
  obtain ⟨final, formed, finalHeap, finalReg, finalStack, finalOutput, finalPC, finalActive⟩ :=
    SourceGateFieldFormation.inputConstant_execution machine ready channel (offset + 2 * index) (base + 5)
      address (by rw [readyHeap]; exact valid) (by simpa only [readyHeap, channel] using stored)
      readyPC readyActive (by omega) (by rw [readyHeap]; exact room) sourceBlock
  have readyLive : ready.liveWords = 5 + heap.size := by
    simp [State.liveWords, readyHeap, readyStack, readyOutput]
    omega
  have trace := (first.append copied).append formed
  rw [readyLive] at trace
  refine ⟨final, ?_, ?_, finalStack.trans readyStack, finalOutput.trans readyOutput, ?_, finalActive⟩
  · convert trace using 1 <;> omega
  · simpa only [readyHeap, channel] using finalHeap
  · simpa only [Nat.add_assoc] using finalPC

end Controller.Cost.ForestGraphDirectory
