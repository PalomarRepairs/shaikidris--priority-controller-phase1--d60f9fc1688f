module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.Model

@[expose] public section

/-! A concrete four-word serialization of indexed-machine instructions.
Decoding uniqueness and operand capacity are representation results. Generating
these words by a fetched compiler is a separate executable obligation. -/
namespace Controller.Cost.InstructionEncoding

/-- Fixed-width records retain every operand and use zero padding. -/
def fields : Instruction width registers → List Nat
  | .constant dst value => [0, dst.val, value.val, 0]
  | .copy dst src => [1, dst.val, src.val, 0]
  | .add dst left right => [2, dst.val, left.val, right.val]
  | .xor dst left right => [3, dst.val, left.val, right.val]
  | .load dst address => [4, dst.val, address.val, 0]
  | .store address src => [5, address.val, src.val, 0]
  | .allocate src => [6, src.val, 0, 0]
  | .release => [7, 0, 0, 0]
  | .push src => [8, src.val, 0, 0]
  | .pop dst => [9, dst.val, 0, 0]
  | .emit src => [10, src.val, 0, 0]
  | .branchZero src target => [11, src.val, target.val, 0]
  | .halt => [12, 0, 0, 0]

@[simp] theorem fields_length (instruction : Instruction width registers) :
    (fields instruction).length = 4 := by
  cases instruction <;> rfl

theorem fields_injective : Function.Injective
    (fields : Instruction width registers → List Nat) := by
  intro first second same
  cases first <;> cases second <;> simp_all [fields]
  all_goals simpa only [Fin.ext_iff] using same

theorem field_capacity (instruction : Instruction width registers)
    (registerCapacity : registers ≤ 2 ^ width) (opcodeCapacity : 13 ≤ 2 ^ width) :
    ∀ value ∈ fields instruction, value < 2 ^ width := by
  cases instruction <;> simp only [fields, List.mem_cons, List.not_mem_nil, or_false]
  all_goals intro value member
  all_goals rcases member with h | h | h | h <;> subst value
  all_goals omega

/-- Operand conversion is exact when the declared register and opcode spaces fit. -/
def encode (instruction : Instruction width registers) : List (Word width) :=
  (fields instruction).map (word width)

@[simp] theorem encode_length (instruction : Instruction width registers) :
    (encode instruction).length = 4 := by simp [encode]

theorem encode_values (instruction : Instruction width registers)
    (registerCapacity : registers ≤ 2 ^ width) (opcodeCapacity : 13 ≤ 2 ^ width) :
    (encode instruction).map Fin.val = fields instruction := by
  simp only [encode, List.map_map]
  conv_rhs => rw [← List.map_id (fields instruction)]
  apply List.map_congr_left
  intro value member
  exact Nat.mod_eq_of_lt (field_capacity instruction registerCapacity opcodeCapacity value member)

theorem encode_injective (registerCapacity : registers ≤ 2 ^ width)
    (opcodeCapacity : 13 ≤ 2 ^ width) :
    Function.Injective (encode : Instruction width registers → List (Word width)) := by
  intro first second same
  apply fields_injective
  have values := congrArg (List.map Fin.val) same
  simpa only [encode_values _ registerCapacity opcodeCapacity] using values

end Controller.Cost.InstructionEncoding
