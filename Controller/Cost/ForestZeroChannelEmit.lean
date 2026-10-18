module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroDictionary
public import Controller.Cost.ForestZeroModelLift
public import Controller.Horn.WorklistAccept
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Channel projection reads the actual dictionary table and terminal off
cells. Unseen channels produce true; allocated channels produce the complement
of their stored off mark. The fixed loop visits channels in descending order,
so prepending each emitted word produces ascending channel output. Source
header and base-register formation belong to the calling execution. -/
namespace Controller.Cost.ForestZeroChannelEmit
open Controller.Cost Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroDictionary
open Controller.Horn.WorklistStorage Controller.Horn.WorklistOutcome
variable {width channels ambient : Nat}

/-- Registers3/4/7 hold the remaining channel count, dictionary table base and
local off-cell base+1. Zero2, one5 and decrement6 are retained. -/
def code (width entry returnPC : Nat) : Program width 8 :=
  #[.branchZero 3 (word width returnPC), .add 3 3 6,
    .add 0 4 3, .load 0 0, .branchZero 0 (word width (entry + 11)),
    .add 0 0 6, .add 0 0 0, .add 0 0 7, .load 0 0,
    .xor 0 0 5, .branchZero 2 (word width (entry + 12)),
    .copy 0 5, .emit 0, .branchZero 2 (word width entry)]

@[simp] theorem code_size (width entry returnPC : Nat) : (code width entry returnPC).size = 14 := rfl

def CodeAt (program : Program width 8) (entry returnPC : Nat) : Prop :=
  ∀ phase : Fin 14, program[entry + phase.val]? = (code width entry returnPC)[phase.val]?

/-- Exact memory and value correspondence for every original channel. The
allocated branch retains the actual local index and interleaved off cell. -/
structure Stored (heap : Array (Word width)) (table offBase : Nat)
    (slots : Fin channels → Nat) (bits : Fin channels → Bool) : Prop where
  tableBound : table + channels ≤ heap.size
  slotFits : ∀ channel, slots channel < 2 ^ width
  tableCell : ∀ channel, heap[table + channel.val]? = some (word width (slots channel))
  unseen : ∀ channel, slots channel = 0 → bits channel = true
  offBound : ∀ channel, slots channel ≠ 0 → offBase + 2 * (slots channel - 1) < heap.size
  offCell : ∀ channel, slots channel ≠ 0 →
    heap[offBase + 2 * (slots channel - 1)]? =
      some (word width (if bits channel then 0 else 1))

def localValues (queue : List (Fin n)) (index : Nat) : Bool :=
  if valid : index < n then offAssignment queue ⟨index, valid⟩ else true

/-- Dictionary inversion and the terminal physical FIFO derive the projection
representation; an arbitrary bit table is not a source-model premise. -/
theorem stored_from_dictionary (heap : Array (Word width))
    (dictionary : Dictionary ambient) (layout : Layout ambient heap.size)
    (represented : Represented heap layout dictionary)
    (within : channels ≤ ambient) (base : Nat)
    (queue : List (Fin dictionary.coordinates.size))
    (fifo : Controller.Horn.WorklistMark.Stored queue base heap)
    (countFits : dictionary.coordinates.size + 1 < 2 ^ width) :
    Stored heap layout.tableBase (base + 1)
      (fun channel => dictionary.slots[(⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ : Fin ambient).val])
      (fun channel => ForestZeroModelLift.lift dictionary true (localValues queue)
        ⟨channel.val, lt_of_lt_of_le channel.isLt within⟩) := by
  refine ⟨by have := layout.tableBound; omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro channel
    have bound := encoded_bound dictionary represented.coherent
      (⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ : Fin ambient)
    omega
  · intro channel
    exact represented.slots ⟨channel.val, lt_of_lt_of_le channel.isLt within⟩
  · intro channel unseen
    exact ForestZeroModelLift.lift_unseen dictionary true (localValues queue)
      ⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ unseen
  · intro channel used
    have bound := encoded_bound dictionary represented.coherent
      (⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ : Fin ambient)
    have capacity := fifo.fits
    omega
  · intro channel used
    let coordinate : Fin ambient := ⟨channel.val, lt_of_lt_of_le channel.isLt within⟩
    have encodedBound := encoded_bound dictionary represented.coherent coordinate
    change dictionary.slots[coordinate.val] ≠ 0 at used
    have allocated : dictionary.slots[coordinate.val] - 1 < dictionary.coordinates.size := by omega
    let label : Fin dictionary.coordinates.size := ⟨dictionary.slots[coordinate.val] - 1, allocated⟩
    have offBound : offAddress base label < heap.size := by
      have capacity := fifo.fits
      have bound := label.isLt
      unfold offAddress
      omega
    have cell : heap[offAddress base label]? =
        some (word width (if label ∈ queue then 1 else 0)) := by
      rw [Array.getElem?_eq_getElem offBound]
      exact congrArg some (fifo.flags label)
    have address : base + 1 + 2 * (dictionary.slots[coordinate.val] - 1) = offAddress base label := by
      dsimp only [offAddress, label]
      omega
    rw [address]
    by_cases member : label ∈ queue
    · simpa [ForestZeroModelLift.lift, used, localValues, allocated, offAssignment,
        coordinate, label, member] using cell
    · simpa [ForestZeroModelLift.lift, used, localValues, allocated, offAssignment,
        coordinate, label, member] using cell


/-- The output bit occupies scratch register zero; only remaining register
three changes. All other caller registers and memory stay in the template. -/
def configuration (template : State width 8) (cursor remaining : Nat)
    (scratch : Word width) (output : List (Word width)) : State width 8 :=
  { template with
    pc := word width cursor
    reg := fun register => if register = 0 then scratch else
      if register = 3 then word width remaining else template.reg register
    output := output }

def bitWord (width : Nat) (bit : Bool) : Word width := word width (if bit then 1 else 0)

@[simp] theorem configuration_live (template : State width 8) (cursor remaining : Nat)
    (scratch : Word width) (output : List (Word width)) :
    (configuration template cursor remaining scratch output).liveWords =
      9 + template.heap.size + template.stack.length + output.length := by
  simp only [configuration, State.liveWords]
  omega

private theorem fetched (program : Program width 8) (state : State width 8)
    (entry returnPC offset : Nat) (position : state.pc = word width (entry + offset))
    (fits : entry + offset < 2 ^ width) (inside : offset < 14)
    (present : CodeAt program entry returnPC) :
    programStep program state = ((code width entry returnPC)[offset]?).bind
      (fun instruction => step instruction state) := by
  unfold programStep
  rw [position, show (word width (entry + offset)).val = entry + offset from Nat.mod_eq_of_lt fits,
    present ⟨offset, inside⟩]
  rfl

private structure Runtime (template : State width 8) (entry table offBase : Nat) : Prop where
  running : template.halted = false
  zero : template.reg 2 = word width 0
  table : template.reg 4 = word width table
  one : template.reg 5 = word width 1
  decrement : template.reg 6 = word width (2 ^ width - 1)
  offBase : template.reg 7 = word width offBase
  programFits : entry + 14 < 2 ^ width
  heapFits : template.heap.size ≤ 2 ^ width

private structure Cell (template : State width 8) (table offBase remaining slot : Nat)
    (bit : Bool) : Prop where
  countFits : remaining + 1 < 2 ^ width
  tableBound : table + remaining < template.heap.size
  slotFits : slot < 2 ^ width
  tableCell : template.heap[table + remaining]? = some (word width slot)
  unseen : slot = 0 → bit = true
  offBound : slot ≠ 0 → offBase + 2 * (slot - 1) < template.heap.size
  offCell : slot ≠ 0 → template.heap[offBase + 2 * (slot - 1)]? =
    some (word width (if bit then 0 else 1))

private theorem transition_0 (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase remaining slot : Nat) (bit : Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cell : Cell template table offBase remaining slot bit)
    (present : CodeAt program entry returnPC) :
    programStep program (configuration template (entry) (remaining + 1) (scratch) (output)) =
      some (configuration template (entry + 1) (remaining + 1) (scratch) (output)) := by
  have pcFits (offset : Nat) (bound : offset ≤ 14) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) runtime.programFits
  rw [fetched program _ entry returnPC 0 (by rfl) (pcFits 0 (by decide)) (by decide) present]
  have pcValue : (entry + 0) % 2 ^ width = entry + 0 := Nat.mod_eq_of_lt (pcFits 0 (by decide))
  have countValue : (remaining + 1) % 2 ^ width = remaining + 1 := Nat.mod_eq_of_lt cell.countFits
  have remainingValue : remaining % 2 ^ width = remaining := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have tableValue : table % 2 ^ width = table := Nat.mod_eq_of_lt (by have := cell.tableBound; have := runtime.heapFits; omega)
  have addressValue : (table + remaining) % 2 ^ width = table + remaining :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le cell.tableBound runtime.heapFits)
  have slotValue : slot % 2 ^ width = slot := Nat.mod_eq_of_lt cell.slotFits
  have oneValue : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have zeroValue : 0 % 2 ^ width = 0 := Nat.zero_mod _
  have decrementValue : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  simp [step, code, configuration, State.advance, State.put, runtime.running, runtime.zero, runtime.table, runtime.one, runtime.decrement, runtime.offBase, word, pcValue, countValue, remainingValue, tableValue, addressValue, slotValue, oneValue, zeroValue, decrementValue, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_1 (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase remaining slot : Nat) (bit : Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cell : Cell template table offBase remaining slot bit)
    (present : CodeAt program entry returnPC) :
    programStep program (configuration template (entry + 1) (remaining + 1) (scratch) (output)) =
      some (configuration template (entry + 2) (remaining) (scratch) (output)) := by
  have pcFits (offset : Nat) (bound : offset ≤ 14) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) runtime.programFits
  rw [fetched program _ entry returnPC 1 (by rfl) (pcFits 1 (by decide)) (by decide) present]
  have pcValue : (entry + 1) % 2 ^ width = entry + 1 := Nat.mod_eq_of_lt (pcFits 1 (by decide))
  have countValue : (remaining + 1) % 2 ^ width = remaining + 1 := Nat.mod_eq_of_lt cell.countFits
  have remainingValue : remaining % 2 ^ width = remaining := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have tableValue : table % 2 ^ width = table := Nat.mod_eq_of_lt (by have := cell.tableBound; have := runtime.heapFits; omega)
  have addressValue : (table + remaining) % 2 ^ width = table + remaining :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le cell.tableBound runtime.heapFits)
  have slotValue : slot % 2 ^ width = slot := Nat.mod_eq_of_lt cell.slotFits
  have oneValue : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have zeroValue : 0 % 2 ^ width = 0 := Nat.zero_mod _
  have decrementValue : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  have sumEq : remaining + 1 + (2 ^ width - 1) = 2 ^ width + remaining := by
    have := Nat.two_pow_pos width
    omega
  have arithmetic : (remaining + (1 + (2 ^ width - 1))) % 2 ^ width = remaining := by
    rw [← Nat.add_assoc, sumEq, Nat.add_mod_left, remainingValue]
  simp [step, code, configuration, State.advance, State.put, runtime.running, runtime.zero, runtime.table, runtime.one, runtime.decrement, runtime.offBase, word, pcValue, countValue, remainingValue, tableValue, addressValue, slotValue, oneValue, zeroValue, decrementValue, Nat.add_assoc, arithmetic]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_2 (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase remaining slot : Nat) (bit : Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cell : Cell template table offBase remaining slot bit)
    (present : CodeAt program entry returnPC) :
    programStep program (configuration template (entry + 2) (remaining) (scratch) (output)) =
      some (configuration template (entry + 3) (remaining) (word width (table + remaining)) (output)) := by
  have pcFits (offset : Nat) (bound : offset ≤ 14) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) runtime.programFits
  rw [fetched program _ entry returnPC 2 (by rfl) (pcFits 2 (by decide)) (by decide) present]
  have pcValue : (entry + 2) % 2 ^ width = entry + 2 := Nat.mod_eq_of_lt (pcFits 2 (by decide))
  have countValue : (remaining + 1) % 2 ^ width = remaining + 1 := Nat.mod_eq_of_lt cell.countFits
  have remainingValue : remaining % 2 ^ width = remaining := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have tableValue : table % 2 ^ width = table := Nat.mod_eq_of_lt (by have := cell.tableBound; have := runtime.heapFits; omega)
  have addressValue : (table + remaining) % 2 ^ width = table + remaining :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le cell.tableBound runtime.heapFits)
  have slotValue : slot % 2 ^ width = slot := Nat.mod_eq_of_lt cell.slotFits
  have oneValue : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have zeroValue : 0 % 2 ^ width = 0 := Nat.zero_mod _
  have decrementValue : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  simp [step, code, configuration, State.advance, State.put, runtime.running, runtime.zero, runtime.table, runtime.one, runtime.decrement, runtime.offBase, word, pcValue, countValue, remainingValue, tableValue, addressValue, slotValue, oneValue, zeroValue, decrementValue, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_3 (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase remaining slot : Nat) (bit : Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cell : Cell template table offBase remaining slot bit)
    (present : CodeAt program entry returnPC) :
    programStep program (configuration template (entry + 3) (remaining) (word width (table + remaining)) (output)) =
      some (configuration template (entry + 4) (remaining) (word width (slot)) (output)) := by
  have pcFits (offset : Nat) (bound : offset ≤ 14) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) runtime.programFits
  rw [fetched program _ entry returnPC 3 (by rfl) (pcFits 3 (by decide)) (by decide) present]
  have pcValue : (entry + 3) % 2 ^ width = entry + 3 := Nat.mod_eq_of_lt (pcFits 3 (by decide))
  have countValue : (remaining + 1) % 2 ^ width = remaining + 1 := Nat.mod_eq_of_lt cell.countFits
  have remainingValue : remaining % 2 ^ width = remaining := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have tableValue : table % 2 ^ width = table := Nat.mod_eq_of_lt (by have := cell.tableBound; have := runtime.heapFits; omega)
  have addressValue : (table + remaining) % 2 ^ width = table + remaining :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le cell.tableBound runtime.heapFits)
  have slotValue : slot % 2 ^ width = slot := Nat.mod_eq_of_lt cell.slotFits
  have oneValue : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have zeroValue : 0 % 2 ^ width = 0 := Nat.zero_mod _
  have decrementValue : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  have tableCell : template.heap[table + remaining]'cell.tableBound = word width slot := by
    have stored := cell.tableCell
    rw [Array.getElem?_eq_getElem cell.tableBound] at stored
    exact Option.some.inj stored
  simp [step, code, configuration, State.advance, State.put, runtime.running, runtime.zero, runtime.table, runtime.one, runtime.decrement, runtime.offBase, word, pcValue, countValue, remainingValue, tableValue, addressValue, slotValue, oneValue, zeroValue, decrementValue, Nat.add_assoc, cell.tableBound, tableCell]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_4_seen (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase remaining slot : Nat) (bit : Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cell : Cell template table offBase remaining slot bit)
    (present : CodeAt program entry returnPC) (seen : slot ≠ 0) :
    programStep program (configuration template (entry + 4) (remaining) (word width (slot)) (output)) =
      some (configuration template (entry + 5) (remaining) (word width (slot)) (output)) := by
  have pcFits (offset : Nat) (bound : offset ≤ 14) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) runtime.programFits
  rw [fetched program _ entry returnPC 4 (by rfl) (pcFits 4 (by decide)) (by decide) present]
  have pcValue : (entry + 4) % 2 ^ width = entry + 4 := Nat.mod_eq_of_lt (pcFits 4 (by decide))
  have countValue : (remaining + 1) % 2 ^ width = remaining + 1 := Nat.mod_eq_of_lt cell.countFits
  have remainingValue : remaining % 2 ^ width = remaining := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have tableValue : table % 2 ^ width = table := Nat.mod_eq_of_lt (by have := cell.tableBound; have := runtime.heapFits; omega)
  have addressValue : (table + remaining) % 2 ^ width = table + remaining :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le cell.tableBound runtime.heapFits)
  have slotValue : slot % 2 ^ width = slot := Nat.mod_eq_of_lt cell.slotFits
  have oneValue : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have zeroValue : 0 % 2 ^ width = 0 := Nat.zero_mod _
  have decrementValue : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  simp [step, code, configuration, State.advance, State.put, runtime.running, runtime.zero, runtime.table, runtime.one, runtime.decrement, runtime.offBase, word, pcValue, countValue, remainingValue, tableValue, addressValue, slotValue, oneValue, zeroValue, decrementValue, Nat.add_assoc, seen]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_4_unseen (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase remaining slot : Nat) (bit : Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cell : Cell template table offBase remaining slot bit)
    (present : CodeAt program entry returnPC) (unseen : slot = 0) :
    programStep program (configuration template (entry + 4) (remaining) (word width (slot)) (output)) =
      some (configuration template (entry + 11) (remaining) (word width (slot)) (output)) := by
  have pcFits (offset : Nat) (bound : offset ≤ 14) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) runtime.programFits
  rw [fetched program _ entry returnPC 4 (by rfl) (pcFits 4 (by decide)) (by decide) present]
  have pcValue : (entry + 4) % 2 ^ width = entry + 4 := Nat.mod_eq_of_lt (pcFits 4 (by decide))
  have countValue : (remaining + 1) % 2 ^ width = remaining + 1 := Nat.mod_eq_of_lt cell.countFits
  have remainingValue : remaining % 2 ^ width = remaining := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have tableValue : table % 2 ^ width = table := Nat.mod_eq_of_lt (by have := cell.tableBound; have := runtime.heapFits; omega)
  have addressValue : (table + remaining) % 2 ^ width = table + remaining :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le cell.tableBound runtime.heapFits)
  have slotValue : slot % 2 ^ width = slot := Nat.mod_eq_of_lt cell.slotFits
  have oneValue : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have zeroValue : 0 % 2 ^ width = 0 := Nat.zero_mod _
  have decrementValue : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  simp [step, code, configuration, State.advance, State.put, runtime.running, runtime.zero, runtime.table, runtime.one, runtime.decrement, runtime.offBase, word, pcValue, countValue, remainingValue, tableValue, addressValue, slotValue, oneValue, zeroValue, decrementValue, Nat.add_assoc, unseen]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_5 (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase remaining slot : Nat) (bit : Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cell : Cell template table offBase remaining slot bit)
    (present : CodeAt program entry returnPC) (seen : slot ≠ 0) :
    programStep program (configuration template (entry + 5) (remaining) (word width (slot)) (output)) =
      some (configuration template (entry + 6) (remaining) (word width (slot - 1)) (output)) := by
  have pcFits (offset : Nat) (bound : offset ≤ 14) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) runtime.programFits
  rw [fetched program _ entry returnPC 5 (by rfl) (pcFits 5 (by decide)) (by decide) present]
  have pcValue : (entry + 5) % 2 ^ width = entry + 5 := Nat.mod_eq_of_lt (pcFits 5 (by decide))
  have countValue : (remaining + 1) % 2 ^ width = remaining + 1 := Nat.mod_eq_of_lt cell.countFits
  have remainingValue : remaining % 2 ^ width = remaining := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have tableValue : table % 2 ^ width = table := Nat.mod_eq_of_lt (by have := cell.tableBound; have := runtime.heapFits; omega)
  have addressValue : (table + remaining) % 2 ^ width = table + remaining :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le cell.tableBound runtime.heapFits)
  have slotValue : slot % 2 ^ width = slot := Nat.mod_eq_of_lt cell.slotFits
  have oneValue : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have zeroValue : 0 % 2 ^ width = 0 := Nat.zero_mod _
  have decrementValue : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  have twiceSum : slot - 1 + (slot - 1) = 2 * (slot - 1) := by omega
  have offSum : 2 * (slot - 1) + offBase = offBase + 2 * (slot - 1) := by omega
  have allocatedBound := cell.offBound seen
  have indexValue : (slot - 1) % 2 ^ width = slot - 1 := Nat.mod_eq_of_lt (by omega)
  have twiceValue : (2 * (slot - 1)) % 2 ^ width = 2 * (slot - 1) :=
    Nat.mod_eq_of_lt (by have := runtime.heapFits; omega)
  have offBaseValue : offBase % 2 ^ width = offBase :=
    Nat.mod_eq_of_lt (by have := runtime.heapFits; omega)
  have offAddressValue : (offBase + 2 * (slot - 1)) % 2 ^ width = offBase + 2 * (slot - 1) :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le allocatedBound runtime.heapFits)
  have sumEq : slot + (2 ^ width - 1) = 2 ^ width + (slot - 1) := by omega
  have arithmetic : (slot + (2 ^ width - 1)) % 2 ^ width = slot - 1 := by
    rw [sumEq, Nat.add_mod_left, indexValue]
  simp [step, code, configuration, State.advance, State.put, runtime.running, runtime.zero, runtime.table, runtime.one, runtime.decrement, runtime.offBase, word, pcValue, countValue, remainingValue, tableValue, addressValue, slotValue, oneValue, zeroValue, decrementValue, Nat.add_assoc, seen, arithmetic, indexValue, twiceValue, offBaseValue, offAddressValue, allocatedBound, twiceSum, offSum]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_6 (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase remaining slot : Nat) (bit : Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cell : Cell template table offBase remaining slot bit)
    (present : CodeAt program entry returnPC) (seen : slot ≠ 0) :
    programStep program (configuration template (entry + 6) (remaining) (word width (slot - 1)) (output)) =
      some (configuration template (entry + 7) (remaining) (word width (2 * (slot - 1))) (output)) := by
  have pcFits (offset : Nat) (bound : offset ≤ 14) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) runtime.programFits
  rw [fetched program _ entry returnPC 6 (by rfl) (pcFits 6 (by decide)) (by decide) present]
  have pcValue : (entry + 6) % 2 ^ width = entry + 6 := Nat.mod_eq_of_lt (pcFits 6 (by decide))
  have countValue : (remaining + 1) % 2 ^ width = remaining + 1 := Nat.mod_eq_of_lt cell.countFits
  have remainingValue : remaining % 2 ^ width = remaining := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have tableValue : table % 2 ^ width = table := Nat.mod_eq_of_lt (by have := cell.tableBound; have := runtime.heapFits; omega)
  have addressValue : (table + remaining) % 2 ^ width = table + remaining :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le cell.tableBound runtime.heapFits)
  have slotValue : slot % 2 ^ width = slot := Nat.mod_eq_of_lt cell.slotFits
  have oneValue : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have zeroValue : 0 % 2 ^ width = 0 := Nat.zero_mod _
  have decrementValue : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  have twiceSum : slot - 1 + (slot - 1) = 2 * (slot - 1) := by omega
  have offSum : 2 * (slot - 1) + offBase = offBase + 2 * (slot - 1) := by omega
  have allocatedBound := cell.offBound seen
  have indexValue : (slot - 1) % 2 ^ width = slot - 1 := Nat.mod_eq_of_lt (by omega)
  have twiceValue : (2 * (slot - 1)) % 2 ^ width = 2 * (slot - 1) :=
    Nat.mod_eq_of_lt (by have := runtime.heapFits; omega)
  have offBaseValue : offBase % 2 ^ width = offBase :=
    Nat.mod_eq_of_lt (by have := runtime.heapFits; omega)
  have offAddressValue : (offBase + 2 * (slot - 1)) % 2 ^ width = offBase + 2 * (slot - 1) :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le allocatedBound runtime.heapFits)
  simp [step, code, configuration, State.advance, State.put, runtime.running, runtime.zero, runtime.table, runtime.one, runtime.decrement, runtime.offBase, word, pcValue, countValue, remainingValue, tableValue, addressValue, slotValue, oneValue, zeroValue, decrementValue, Nat.add_assoc, seen, indexValue, twiceValue, offBaseValue, offAddressValue, allocatedBound, twiceSum, offSum]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_7 (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase remaining slot : Nat) (bit : Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cell : Cell template table offBase remaining slot bit)
    (present : CodeAt program entry returnPC) (seen : slot ≠ 0) :
    programStep program (configuration template (entry + 7) (remaining) (word width (2 * (slot - 1))) (output)) =
      some (configuration template (entry + 8) (remaining) (word width (offBase + 2 * (slot - 1))) (output)) := by
  have pcFits (offset : Nat) (bound : offset ≤ 14) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) runtime.programFits
  rw [fetched program _ entry returnPC 7 (by rfl) (pcFits 7 (by decide)) (by decide) present]
  have pcValue : (entry + 7) % 2 ^ width = entry + 7 := Nat.mod_eq_of_lt (pcFits 7 (by decide))
  have countValue : (remaining + 1) % 2 ^ width = remaining + 1 := Nat.mod_eq_of_lt cell.countFits
  have remainingValue : remaining % 2 ^ width = remaining := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have tableValue : table % 2 ^ width = table := Nat.mod_eq_of_lt (by have := cell.tableBound; have := runtime.heapFits; omega)
  have addressValue : (table + remaining) % 2 ^ width = table + remaining :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le cell.tableBound runtime.heapFits)
  have slotValue : slot % 2 ^ width = slot := Nat.mod_eq_of_lt cell.slotFits
  have oneValue : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have zeroValue : 0 % 2 ^ width = 0 := Nat.zero_mod _
  have decrementValue : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  have twiceSum : slot - 1 + (slot - 1) = 2 * (slot - 1) := by omega
  have offSum : 2 * (slot - 1) + offBase = offBase + 2 * (slot - 1) := by omega
  have allocatedBound := cell.offBound seen
  have indexValue : (slot - 1) % 2 ^ width = slot - 1 := Nat.mod_eq_of_lt (by omega)
  have twiceValue : (2 * (slot - 1)) % 2 ^ width = 2 * (slot - 1) :=
    Nat.mod_eq_of_lt (by have := runtime.heapFits; omega)
  have offBaseValue : offBase % 2 ^ width = offBase :=
    Nat.mod_eq_of_lt (by have := runtime.heapFits; omega)
  have offAddressValue : (offBase + 2 * (slot - 1)) % 2 ^ width = offBase + 2 * (slot - 1) :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le allocatedBound runtime.heapFits)
  simp [step, code, configuration, State.advance, State.put, runtime.running, runtime.zero, runtime.table, runtime.one, runtime.decrement, runtime.offBase, word, pcValue, countValue, remainingValue, tableValue, addressValue, slotValue, oneValue, zeroValue, decrementValue, Nat.add_assoc, seen, indexValue, twiceValue, offBaseValue, offAddressValue, allocatedBound, twiceSum, offSum]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_8 (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase remaining slot : Nat) (bit : Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cell : Cell template table offBase remaining slot bit)
    (present : CodeAt program entry returnPC) (seen : slot ≠ 0) :
    programStep program (configuration template (entry + 8) (remaining) (word width (offBase + 2 * (slot - 1))) (output)) =
      some (configuration template (entry + 9) (remaining) (word width (if bit then 0 else 1)) (output)) := by
  have pcFits (offset : Nat) (bound : offset ≤ 14) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) runtime.programFits
  rw [fetched program _ entry returnPC 8 (by rfl) (pcFits 8 (by decide)) (by decide) present]
  have pcValue : (entry + 8) % 2 ^ width = entry + 8 := Nat.mod_eq_of_lt (pcFits 8 (by decide))
  have countValue : (remaining + 1) % 2 ^ width = remaining + 1 := Nat.mod_eq_of_lt cell.countFits
  have remainingValue : remaining % 2 ^ width = remaining := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have tableValue : table % 2 ^ width = table := Nat.mod_eq_of_lt (by have := cell.tableBound; have := runtime.heapFits; omega)
  have addressValue : (table + remaining) % 2 ^ width = table + remaining :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le cell.tableBound runtime.heapFits)
  have slotValue : slot % 2 ^ width = slot := Nat.mod_eq_of_lt cell.slotFits
  have oneValue : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have zeroValue : 0 % 2 ^ width = 0 := Nat.zero_mod _
  have decrementValue : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  have twiceSum : slot - 1 + (slot - 1) = 2 * (slot - 1) := by omega
  have offSum : 2 * (slot - 1) + offBase = offBase + 2 * (slot - 1) := by omega
  have allocatedBound := cell.offBound seen
  have indexValue : (slot - 1) % 2 ^ width = slot - 1 := Nat.mod_eq_of_lt (by omega)
  have twiceValue : (2 * (slot - 1)) % 2 ^ width = 2 * (slot - 1) :=
    Nat.mod_eq_of_lt (by have := runtime.heapFits; omega)
  have offBaseValue : offBase % 2 ^ width = offBase :=
    Nat.mod_eq_of_lt (by have := runtime.heapFits; omega)
  have offAddressValue : (offBase + 2 * (slot - 1)) % 2 ^ width = offBase + 2 * (slot - 1) :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le allocatedBound runtime.heapFits)
  have offCell : template.heap[offBase + 2 * (slot - 1)]'allocatedBound =
      word width (if bit then 0 else 1) := by
    have stored := cell.offCell seen
    rw [Array.getElem?_eq_getElem allocatedBound] at stored
    exact Option.some.inj stored
  simp [step, code, configuration, State.advance, State.put, runtime.running, runtime.zero, runtime.table, runtime.one, runtime.decrement, runtime.offBase, word, pcValue, countValue, remainingValue, tableValue, addressValue, slotValue, oneValue, zeroValue, decrementValue, Nat.add_assoc, seen, indexValue, twiceValue, offBaseValue, offAddressValue, allocatedBound, twiceSum, offSum, offCell]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_9 (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase remaining slot : Nat) (bit : Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cell : Cell template table offBase remaining slot bit)
    (present : CodeAt program entry returnPC) :
    programStep program (configuration template (entry + 9) (remaining) (word width (if bit then 0 else 1)) (output)) =
      some (configuration template (entry + 10) (remaining) (bitWord width bit) (output)) := by
  have pcFits (offset : Nat) (bound : offset ≤ 14) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) runtime.programFits
  rw [fetched program _ entry returnPC 9 (by rfl) (pcFits 9 (by decide)) (by decide) present]
  have pcValue : (entry + 9) % 2 ^ width = entry + 9 := Nat.mod_eq_of_lt (pcFits 9 (by decide))
  have countValue : (remaining + 1) % 2 ^ width = remaining + 1 := Nat.mod_eq_of_lt cell.countFits
  have remainingValue : remaining % 2 ^ width = remaining := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have tableValue : table % 2 ^ width = table := Nat.mod_eq_of_lt (by have := cell.tableBound; have := runtime.heapFits; omega)
  have addressValue : (table + remaining) % 2 ^ width = table + remaining :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le cell.tableBound runtime.heapFits)
  have slotValue : slot % 2 ^ width = slot := Nat.mod_eq_of_lt cell.slotFits
  have oneValue : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have zeroValue : 0 % 2 ^ width = 0 := Nat.zero_mod _
  have decrementValue : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  cases bit <;>
  simp [step, code, configuration, State.advance, State.put, runtime.running, runtime.zero, runtime.table, runtime.one, runtime.decrement, runtime.offBase, word, pcValue, countValue, remainingValue, tableValue, addressValue, slotValue, oneValue, zeroValue, decrementValue, Nat.add_assoc, bitWord]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_10 (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase remaining slot : Nat) (bit : Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cell : Cell template table offBase remaining slot bit)
    (present : CodeAt program entry returnPC) :
    programStep program (configuration template (entry + 10) (remaining) (bitWord width bit) (output)) =
      some (configuration template (entry + 12) (remaining) (bitWord width bit) (output)) := by
  have pcFits (offset : Nat) (bound : offset ≤ 14) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) runtime.programFits
  rw [fetched program _ entry returnPC 10 (by rfl) (pcFits 10 (by decide)) (by decide) present]
  have pcValue : (entry + 10) % 2 ^ width = entry + 10 := Nat.mod_eq_of_lt (pcFits 10 (by decide))
  have countValue : (remaining + 1) % 2 ^ width = remaining + 1 := Nat.mod_eq_of_lt cell.countFits
  have remainingValue : remaining % 2 ^ width = remaining := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have tableValue : table % 2 ^ width = table := Nat.mod_eq_of_lt (by have := cell.tableBound; have := runtime.heapFits; omega)
  have addressValue : (table + remaining) % 2 ^ width = table + remaining :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le cell.tableBound runtime.heapFits)
  have slotValue : slot % 2 ^ width = slot := Nat.mod_eq_of_lt cell.slotFits
  have oneValue : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have zeroValue : 0 % 2 ^ width = 0 := Nat.zero_mod _
  have decrementValue : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  simp [step, code, configuration, State.advance, State.put, runtime.running, runtime.zero, runtime.table, runtime.one, runtime.decrement, runtime.offBase, word, pcValue, countValue, remainingValue, tableValue, addressValue, slotValue, oneValue, zeroValue, decrementValue, Nat.add_assoc, bitWord]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_11 (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase remaining slot : Nat) (bit : Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cell : Cell template table offBase remaining slot bit)
    (present : CodeAt program entry returnPC) (unseen : slot = 0) :
    programStep program (configuration template (entry + 11) (remaining) (word width (slot)) (output)) =
      some (configuration template (entry + 12) (remaining) (bitWord width bit) (output)) := by
  have pcFits (offset : Nat) (bound : offset ≤ 14) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) runtime.programFits
  rw [fetched program _ entry returnPC 11 (by rfl) (pcFits 11 (by decide)) (by decide) present]
  have pcValue : (entry + 11) % 2 ^ width = entry + 11 := Nat.mod_eq_of_lt (pcFits 11 (by decide))
  have countValue : (remaining + 1) % 2 ^ width = remaining + 1 := Nat.mod_eq_of_lt cell.countFits
  have remainingValue : remaining % 2 ^ width = remaining := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have tableValue : table % 2 ^ width = table := Nat.mod_eq_of_lt (by have := cell.tableBound; have := runtime.heapFits; omega)
  have addressValue : (table + remaining) % 2 ^ width = table + remaining :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le cell.tableBound runtime.heapFits)
  have slotValue : slot % 2 ^ width = slot := Nat.mod_eq_of_lt cell.slotFits
  have oneValue : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have zeroValue : 0 % 2 ^ width = 0 := Nat.zero_mod _
  have decrementValue : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  have bitTrue := cell.unseen unseen
  simp [step, code, configuration, State.advance, State.put, runtime.running, runtime.zero, runtime.table, runtime.one, runtime.decrement, runtime.offBase, word, pcValue, countValue, remainingValue, tableValue, addressValue, slotValue, oneValue, zeroValue, decrementValue, Nat.add_assoc, unseen, bitWord, bitTrue]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_12 (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase remaining slot : Nat) (bit : Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cell : Cell template table offBase remaining slot bit)
    (present : CodeAt program entry returnPC) :
    programStep program (configuration template (entry + 12) (remaining) (bitWord width bit) (output)) =
      some (configuration template (entry + 13) (remaining) (bitWord width bit) (bitWord width bit :: output)) := by
  have pcFits (offset : Nat) (bound : offset ≤ 14) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) runtime.programFits
  rw [fetched program _ entry returnPC 12 (by rfl) (pcFits 12 (by decide)) (by decide) present]
  have pcValue : (entry + 12) % 2 ^ width = entry + 12 := Nat.mod_eq_of_lt (pcFits 12 (by decide))
  have countValue : (remaining + 1) % 2 ^ width = remaining + 1 := Nat.mod_eq_of_lt cell.countFits
  have remainingValue : remaining % 2 ^ width = remaining := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have tableValue : table % 2 ^ width = table := Nat.mod_eq_of_lt (by have := cell.tableBound; have := runtime.heapFits; omega)
  have addressValue : (table + remaining) % 2 ^ width = table + remaining :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le cell.tableBound runtime.heapFits)
  have slotValue : slot % 2 ^ width = slot := Nat.mod_eq_of_lt cell.slotFits
  have oneValue : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have zeroValue : 0 % 2 ^ width = 0 := Nat.zero_mod _
  have decrementValue : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  simp [step, code, configuration, State.advance, State.put, runtime.running, runtime.zero, runtime.table, runtime.one, runtime.decrement, runtime.offBase, word, pcValue, countValue, remainingValue, tableValue, addressValue, slotValue, oneValue, zeroValue, decrementValue, Nat.add_assoc, bitWord]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_13 (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase remaining slot : Nat) (bit : Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cell : Cell template table offBase remaining slot bit)
    (present : CodeAt program entry returnPC) :
    programStep program (configuration template (entry + 13) (remaining) (bitWord width bit) (bitWord width bit :: output)) =
      some (configuration template (entry) (remaining) (bitWord width bit) (bitWord width bit :: output)) := by
  have pcFits (offset : Nat) (bound : offset ≤ 14) : entry + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound entry) runtime.programFits
  rw [fetched program _ entry returnPC 13 (by rfl) (pcFits 13 (by decide)) (by decide) present]
  have pcValue : (entry + 13) % 2 ^ width = entry + 13 := Nat.mod_eq_of_lt (pcFits 13 (by decide))
  have countValue : (remaining + 1) % 2 ^ width = remaining + 1 := Nat.mod_eq_of_lt cell.countFits
  have remainingValue : remaining % 2 ^ width = remaining := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have tableValue : table % 2 ^ width = table := Nat.mod_eq_of_lt (by have := cell.tableBound; have := runtime.heapFits; omega)
  have addressValue : (table + remaining) % 2 ^ width = table + remaining :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le cell.tableBound runtime.heapFits)
  have slotValue : slot % 2 ^ width = slot := Nat.mod_eq_of_lt cell.slotFits
  have oneValue : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (by have := cell.countFits; omega)
  have zeroValue : 0 % 2 ^ width = 0 := Nat.zero_mod _
  have decrementValue : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  simp [step, code, configuration, State.advance, State.put, runtime.running, runtime.zero, runtime.table, runtime.one, runtime.decrement, runtime.offBase, word, pcValue, countValue, remainingValue, tableValue, addressValue, slotValue, oneValue, zeroValue, decrementValue, Nat.add_assoc, bitWord]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)


private theorem prefix_execution (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase remaining slot : Nat) (bit : Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cell : Cell template table offBase remaining slot bit)
    (present : CodeAt program entry returnPC) :
    Execution program (configuration template (entry) (remaining + 1) (scratch) (output))
      (configuration template (entry + 4) (remaining) (word width (slot)) (output)) 4 (9 + template.heap.size + template.stack.length + output.length) := by
  have t0 := transition_0 program template entry returnPC table offBase remaining slot bit scratch output runtime cell present
  have t1 := transition_1 program template entry returnPC table offBase remaining slot bit scratch output runtime cell present
  have t2 := transition_2 program template entry returnPC table offBase remaining slot bit scratch output runtime cell present
  have t3 := transition_3 program template entry returnPC table offBase remaining slot bit scratch output runtime cell present
  have trace := (Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.refl (configuration template (entry + 4) (remaining) (word width (slot)) (output)))))))
  convert trace using 1 <;> simp only [configuration_live, List.length_cons, Nat.max_self]
  all_goals omega

private theorem allocated_first_execution (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase remaining slot : Nat) (bit : Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cell : Cell template table offBase remaining slot bit)
    (present : CodeAt program entry returnPC) (seen : slot ≠ 0) :
    Execution program (configuration template (entry + 4) (remaining) (word width (slot)) (output))
      (configuration template (entry + 7) (remaining) (word width (2 * (slot - 1))) (output)) 3 (9 + template.heap.size + template.stack.length + output.length) := by
  have t0 := transition_4_seen program template entry returnPC table offBase remaining slot bit scratch output runtime cell present seen
  have t1 := transition_5 program template entry returnPC table offBase remaining slot bit scratch output runtime cell present seen
  have t2 := transition_6 program template entry returnPC table offBase remaining slot bit scratch output runtime cell present seen
  have trace := (Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl (configuration template (entry + 7) (remaining) (word width (2 * (slot - 1))) (output))))))
  convert trace using 1 <;> simp only [configuration_live, List.length_cons, Nat.max_self]
  all_goals omega

private theorem allocated_second_execution (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase remaining slot : Nat) (bit : Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cell : Cell template table offBase remaining slot bit)
    (present : CodeAt program entry returnPC) (seen : slot ≠ 0) :
    Execution program (configuration template (entry + 7) (remaining) (word width (2 * (slot - 1))) (output))
      (configuration template (entry + 10) (remaining) (bitWord width bit) (output)) 3 (9 + template.heap.size + template.stack.length + output.length) := by
  have t0 := transition_7 program template entry returnPC table offBase remaining slot bit scratch output runtime cell present seen
  have t1 := transition_8 program template entry returnPC table offBase remaining slot bit scratch output runtime cell present seen
  have t2 := transition_9 program template entry returnPC table offBase remaining slot bit scratch output runtime cell present
  have trace := (Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl (configuration template (entry + 10) (remaining) (bitWord width bit) (output))))))
  convert trace using 1 <;> simp only [configuration_live, List.length_cons, Nat.max_self]
  all_goals omega

private theorem allocated_last_execution (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase remaining slot : Nat) (bit : Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cell : Cell template table offBase remaining slot bit)
    (present : CodeAt program entry returnPC) :
    Execution program (configuration template (entry + 10) (remaining) (bitWord width bit) (output))
      (configuration template (entry) (remaining) (bitWord width bit) (bitWord width bit :: output)) 3 (9 + template.heap.size + template.stack.length + output.length + 1) := by
  have t0 := transition_10 program template entry returnPC table offBase remaining slot bit scratch output runtime cell present
  have t1 := transition_12 program template entry returnPC table offBase remaining slot bit scratch output runtime cell present
  have t2 := transition_13 program template entry returnPC table offBase remaining slot bit scratch output runtime cell present
  have trace := (Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl (configuration template (entry) (remaining) (bitWord width bit) (bitWord width bit :: output))))))
  convert trace using 1 <;> simp only [configuration_live, List.length_cons, Nat.max_self]
  all_goals omega

private theorem unseen_tail_execution (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase remaining slot : Nat) (bit : Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cell : Cell template table offBase remaining slot bit)
    (present : CodeAt program entry returnPC) (unseen : slot = 0) :
    Execution program (configuration template (entry + 4) (remaining) (word width (slot)) (output))
      (configuration template (entry) (remaining) (bitWord width bit) (bitWord width bit :: output)) 4 (9 + template.heap.size + template.stack.length + output.length + 1) := by
  have t0 := transition_4_unseen program template entry returnPC table offBase remaining slot bit scratch output runtime cell present unseen
  have t1 := transition_11 program template entry returnPC table offBase remaining slot bit scratch output runtime cell present unseen
  have t2 := transition_12 program template entry returnPC table offBase remaining slot bit scratch output runtime cell present
  have t3 := transition_13 program template entry returnPC table offBase remaining slot bit scratch output runtime cell present
  have trace := (Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.refl (configuration template (entry) (remaining) (bitWord width bit) (bitWord width bit :: output)))))))
  convert trace using 1 <;> simp only [configuration_live, List.length_cons, Nat.max_self]
  all_goals omega

/-- A channel is read once from the dictionary. Allocated channels take
thirteen fetched steps; unseen channels take eight. Both append one output. -/
private theorem iteration_execution (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase remaining slot : Nat) (bit : Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cell : Cell template table offBase remaining slot bit)
    (present : CodeAt program entry returnPC) :
    ∃ ticks, Execution program (configuration template (entry) (remaining + 1) (scratch) (output))
      (configuration template (entry) (remaining) (bitWord width bit) (bitWord width bit :: output)) ticks (9 + template.heap.size + template.stack.length + output.length + 1) ∧ ticks ≤ 13 := by
  have initialPart := prefix_execution program template entry returnPC table offBase remaining slot bit
    scratch output runtime cell present
  by_cases unseen : slot = 0
  · have tail := unseen_tail_execution program template entry returnPC table offBase remaining slot bit
      scratch output runtime cell present unseen
    refine ⟨8, ?_, by decide⟩
    convert initialPart.append tail using 1 <;> simp only [Nat.max_eq_right (by omega :
      9 + template.heap.size + template.stack.length + output.length ≤ 9 + template.heap.size + template.stack.length + output.length + 1)]
  · have first := allocated_first_execution program template entry returnPC table offBase remaining slot bit
      scratch output runtime cell present unseen
    have second := allocated_second_execution program template entry returnPC table offBase remaining slot bit
      scratch output runtime cell present unseen
    have last := allocated_last_execution program template entry returnPC table offBase remaining slot bit
      scratch output runtime cell present
    refine ⟨13, ?_, by decide⟩
    convert ((initialPart.append first).append second).append last using 1 <;>
      simp only [Nat.max_self, Nat.max_eq_right (by omega :
        9 + template.heap.size + template.stack.length + output.length ≤ 9 + template.heap.size + template.stack.length + output.length + 1)]

private theorem exit_execution (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase : Nat) (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase) (present : CodeAt program entry returnPC) :
    Execution program (configuration template entry 0 scratch output)
      (configuration template returnPC 0 scratch output) 1
      (9 + template.heap.size + template.stack.length + output.length) := by
  have transition : programStep program (configuration template entry 0 scratch output) =
      some (configuration template returnPC 0 scratch output) := by
    rw [fetched program _ entry returnPC 0 (by simp only [configuration, Nat.add_zero])
      (by have := runtime.programFits; omega) (by decide) present]
    simp [code, step, configuration, runtime.running, State.advance, word]
  simpa only [configuration_live, Nat.max_self] using Execution.cons transition
    (Execution.refl (configuration template returnPC 0 scratch output))

/-- Ascending channel words, represented independently of the execution's
scratch register and descending traversal order. -/
def outputPrefix (width : Nat) (bits : Nat → Bool) (count : Nat) : List (Word width) :=
  (List.range count).map (fun channel => bitWord width (bits channel))

@[simp] theorem outputPrefix_zero (bits : Nat → Bool) : outputPrefix width bits 0 = [] := rfl

@[simp] theorem outputPrefix_succ (bits : Nat → Bool) (count : Nat) :
    outputPrefix width bits (count + 1) = outputPrefix width bits count ++ [bitWord width (bits count)] := by
  simp only [outputPrefix, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- The complete fixed loop charges the actual allocated/unseen branch
lengths and all live emitted words. Repeated local slots remain valid. -/
private theorem loop_execution (program : Program width 8) (template : State width 8)
    (entry returnPC table offBase count : Nat) (slots : Nat → Nat) (bits : Nat → Bool)
    (scratch : Word width) (output : List (Word width))
    (runtime : Runtime template entry table offBase)
    (cells : ∀ channel < count, Cell template table offBase channel (slots channel) (bits channel))
    (present : CodeAt program entry returnPC) :
    ∃ finalScratch ticks peak,
      Execution program (configuration template entry count scratch output)
        (configuration template returnPC 0 finalScratch (outputPrefix width bits count ++ output)) ticks peak ∧
      ticks ≤ 13 * count + 1 ∧
      peak ≤ 9 + template.heap.size + template.stack.length + output.length + count := by
  induction count generalizing scratch output with
  | zero =>
      refine ⟨scratch, 1, 9 + template.heap.size + template.stack.length + output.length, ?_, by omega, by omega⟩
      simpa only [outputPrefix_zero, List.nil_append] using
        exit_execution program template entry returnPC table offBase scratch output runtime present
  | succ count ih =>
      have cell := cells count (by omega)
      obtain ⟨firstTicks, first, firstBound⟩ := iteration_execution program template entry returnPC
        table offBase count (slots count) (bits count) scratch output runtime cell present
      obtain ⟨finalScratch, ticks, peak, rest, timeBound, peakBound⟩ :=
        ih (bitWord width (bits count)) (bitWord width (bits count) :: output)
          (fun channel bound => cells channel (by omega))
      refine ⟨finalScratch, firstTicks + ticks,
        max (9 + template.heap.size + template.stack.length + output.length + 1) peak,
        ?_, by omega, ?_⟩
      · simpa only [outputPrefix_succ, List.append_assoc, List.singleton_append] using first.append rest
      · have lengthEq : (bitWord width (bits count) :: output).length = output.length + 1 := rfl
        rw [lengthEq] at peakBound
        exact max_le (by omega) (by omega)

/-- Complete projection from the physically represented original channel
slots. Header-derived count and bases are supplied by the calling registers. -/
theorem execution (program : Program width 8) (state : State width 8)
    (entry returnPC table offBase : Nat) (slots : Fin channels → Nat) (bits : Fin channels → Bool)
    (stored : Stored state.heap table offBase slots bits)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (remaining : state.reg 3 = word width channels)
    (tableWord : state.reg 4 = word width table) (one : state.reg 5 = word width 1)
    (decrement : state.reg 6 = word width (2 ^ width - 1)) (offWord : state.reg 7 = word width offBase)
    (countFits : channels + 1 < 2 ^ width) (heapFits : state.heap.size ≤ 2 ^ width)
    (programFits : entry + 14 < 2 ^ width) (present : CodeAt program entry returnPC) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 13 * channels + 1 ∧ peak ≤ state.liveWords + channels ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = (List.finRange channels).map (fun channel => bitWord width (bits channel)) ++ state.output ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 3 → final.reg register = state.reg register) ∧
      final.reg 3 = word width 0 ∧ final.pc = word width returnPC ∧ final.halted = false := by
  let extendedSlots : Nat → Nat := fun channel => if valid : channel < channels then slots ⟨channel, valid⟩ else 0
  let extendedBits : Nat → Bool := fun channel => if valid : channel < channels then bits ⟨channel, valid⟩ else true
  have runtime : Runtime state entry table offBase :=
    ⟨running, zero, tableWord, one, decrement, offWord, programFits, heapFits⟩
  have cells (channel : Nat) (valid : channel < channels) :
      Cell state table offBase channel (extendedSlots channel) (extendedBits channel) := by
    let index : Fin channels := ⟨channel, valid⟩
    simpa only [extendedSlots, extendedBits, dite_eq_left valid] using
      (show Cell state table offBase channel (slots index) (bits index) from
        ⟨by omega, by have := stored.tableBound; omega, stored.slotFits index,
          stored.tableCell index, stored.unseen index, stored.offBound index, stored.offCell index⟩)
  obtain ⟨scratch, ticks, peak, trace, timeBound, peakBound⟩ :=
    loop_execution program state entry returnPC table offBase channels extendedSlots extendedBits
      (state.reg 0) state.output runtime cells present
  have initialRegisters :
      (fun register : Fin 8 => if register = 0 then state.reg 0 else
        if register = 3 then word width channels else state.reg register) = state.reg := by
    funext register
    by_cases r0 : register = 0
    · subst register; simp
    · by_cases r3 : register = 3
      · subst register; simpa using remaining.symm
      · simp [r0, r3]
  have initialPc : word width entry = state.pc := position.symm
  have initial : configuration state entry channels (state.reg 0) state.output = state := by
    cases state
    simp only [configuration, initialRegisters, initialPc]
  have words : outputPrefix width extendedBits channels =
      (List.finRange channels).map (fun channel => bitWord width (bits channel)) := by
    apply List.ext_getElem
    · simp [outputPrefix]
    · intro index leftBound rightBound
      have valid : index < channels := by simpa [outputPrefix] using leftBound
      simp [outputPrefix, extendedBits, valid]
  rw [initial] at trace
  refine ⟨_, ticks, peak, trace, timeBound, ?_, rfl, rfl, ?_, ?_, ?_, rfl, ?_⟩
  · change peak ≤ 8 + state.heap.size + state.stack.length + state.output.length + 1 + channels
    omega
  · rw [words]
    rfl
  · intro register r0 r3
    simp only [configuration, ite_eq_right r0, ite_eq_right r3]
  · simp [configuration]
  · exact running


/-- The original-channel output is the actual greatest local FIFO assignment
lifted through the captured dictionary, with true on unseen channels. This
single fetched projection retains the caller's complete heap and saved stack. -/
theorem dictionary_execution (program : Program width 8) (state : State width 8)
    (entry returnPC base : Nat) (dictionary : Dictionary ambient)
    (layout : Layout ambient state.heap.size)
    (represented : Represented state.heap layout dictionary) (within : channels ≤ ambient)
    (queue : List (Fin dictionary.coordinates.size))
    (fifo : Controller.Horn.WorklistMark.Stored queue base state.heap)
    (countFits : dictionary.coordinates.size + 1 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (remaining : state.reg 3 = word width channels)
    (tableWord : state.reg 4 = word width layout.tableBase) (one : state.reg 5 = word width 1)
    (decrement : state.reg 6 = word width (2 ^ width - 1)) (offWord : state.reg 7 = word width (base + 1))
    (channelsFit : channels + 1 < 2 ^ width) (heapFits : state.heap.size ≤ 2 ^ width)
    (programFits : entry + 14 < 2 ^ width) (present : CodeAt program entry returnPC) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 13 * channels + 1 ∧ peak ≤ state.liveWords + channels ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = (List.finRange channels).map (fun channel => bitWord width
        (ForestZeroModelLift.lift dictionary true (localValues queue)
          ⟨channel.val, lt_of_lt_of_le channel.isLt within⟩)) ++ state.output ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 3 → final.reg register = state.reg register) ∧
      final.reg 3 = word width 0 ∧ final.pc = word width returnPC ∧ final.halted = false := by
  exact execution program state entry returnPC layout.tableBase (base + 1) _ _
    (stored_from_dictionary state.heap dictionary layout represented within base queue fifo countFits)
    position running zero remaining tableWord one decrement offWord channelsFit heapFits programFits present

end Controller.Cost.ForestZeroChannelEmit
