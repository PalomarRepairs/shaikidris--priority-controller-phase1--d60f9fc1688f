module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.RawAdapterProgram
public import Controller.Cost.SharedDetectorAssembly

@[expose] public section

/-! A fetched segment can be placed at a later address by translating branch
literals and program counters. Data words, registers, storage and timing are
unchanged by this coordinate translation. -/
namespace Controller.Extensions.ResidentSegment
open Controller.Cost Controller.Cost.RawAdapterProgram

def code (delta : Nat) (instructions : List (Instruction width 8)) : List (Instruction width 8) :=
  instructions.map (relocatedInstruction delta)

@[simp] theorem code_length : (code delta instructions).length = instructions.length := by simp [code]

theorem execution (resident : Program width 8) (instructions : List (Instruction width 8)) (delta : Nat)
    (state final : State width 8) (ticks peak : Nat)
    (position : state.pc = word width delta)
    (present : SharedRootRead.BlockAt resident delta (code delta instructions))
    (capacity : delta+instructions.length<2^width)
    (trace : Execution instructions.toArray { state with pc := word width 0 } final ticks peak) :
    Execution resident state (relocatedState delta final) ticks peak := by
  have physical : ∀ index (valid : index < instructions.toArray.size),
      resident[delta+index]? = some (relocatedInstruction delta (instructions.toArray[index]'valid)) := by
    intro index valid
    have cell := present index (by simpa using valid)
    simpa only [code,List.getElem?_map,List.getElem?_eq_getElem (by simpa using valid),
      Option.map_some,List.getElem_toArray] using cell
  have initial : relocatedState delta { state with pc := word width 0 } = state := by
    change { state with pc := word width ((word width 0).val+delta) } = state
    have zero : (word width 0).val = 0 := by simp [word]
    rw [zero,Nat.zero_add,← position]
  simpa only [initial] using relocated_execution resident instructions.toArray delta physical
    (by simpa using capacity) trace

end Controller.Extensions.ResidentSegment
