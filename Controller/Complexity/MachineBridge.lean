module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.Encoding
public import Controller.Cost.Refinement

@[expose] public section

/-! Binary serialization preserves machine states and fetched programs.
States include registers, heap cells, stack/output words, program counter and
halt flag. Instructions use four opcode bits and framed ordered operands;
programs use a count-delimited instruction stream. Size bounds relate these
encodings to word storage. Operational Turing simulation is separate from
serialization and its endpoint storage bounds. -/
namespace Controller.Complexity.MachineBridge
open Controller.Cost Controller.Complexity.Encoding

def encodeState (state : State width registers) : List Bool :=
  encodeWords width (List.ofFn state.reg) ++
    (encodeWords width state.heap.toList ++
    (encodeWords width state.stack ++
    (encodeWords width state.output ++
    (encodeWords width [state.pc] ++ [state.halted]))))

def decodeState (width registers : Nat) (input : List Bool) : Option (State width registers) := do
  let (values,rest) ← readFramedWords width input
  let (heap,rest) ← readFramedWords width rest
  let (stack,rest) ← readFramedWords width rest
  let (output,rest) ← readFramedWords width rest
  let (control,rest) ← readFramedWords width rest
  match control,rest with
  | [pc],[halted] =>
    if same : values.length=registers then
      some {
        reg := fun i => values[i.val]'(by rw [same]; exact i.isLt)
        heap := heap.toArray
        stack := stack
        output := output
        pc := pc
        halted := halted }
    else none
  | _,_ => none

theorem decode_encode (state : State width registers) : decodeState width registers (encodeState state) = some state := by
  simp only [encodeState,decodeState,readFramedWords_encoded,Bind.bind,Option.bind,
    List.length_ofFn,dite_eq_left True.intro,List.getElem_ofFn,Array.toArray_toList]

def stateEncoding (width registers : Nat) : Computability.Encoding (State width registers) Bool where
  encode := encodeState
  decode := decodeState width registers
  decode_encode := decode_encode

theorem encodeState_length (state : State width registers) :
    (encodeState state).length = (width+1)*state.liveWords+6 := by
  simp only [encodeState,List.length_append,encodeWords_length,List.length_ofFn,Array.length_toList,
    List.length_cons,List.length_nil,State.liveWords,Nat.mul_add,Nat.mul_one,Nat.add_mul,Nat.one_mul]
  omega

theorem encodeState_injective : Function.Injective (encodeState : State width registers → List Bool) :=
  (stateEncoding width registers).encode_injective

@[simp] theorem decodeState_empty : decodeState width registers [] = none := rfl

/-- These bounds concern the actual serialized endpoints of a fetched run. -/
theorem execution_endpoint_bits (program : Program width registers)
    (state final : State width registers) (ticks peak : Nat) (trace : Execution program state final ticks peak) :
    (encodeState state).length ≤ (width+1)*peak+6 ∧ (encodeState final).length ≤ (width+1)*peak+6 := by
  rw [encodeState_length,encodeState_length]
  exact ⟨Nat.add_le_add_right (Nat.mul_le_mul_left _ trace.initial_storage_le) _,
    Nat.add_le_add_right (Nat.mul_le_mul_left _ trace.final_storage_le) _⟩

end Controller.Complexity.MachineBridge

namespace Controller.Complexity.InstructionCodec
open Controller.Cost Controller.Complexity.Encoding

def registerWord (bound : registers ≤ 2^width) (register : Fin registers) : Word width :=
  ⟨register.val, register.isLt.trans_le bound⟩

def readRegister (value : Word width) : Option (Fin registers) :=
  if h : value.val < registers then some ⟨value.val, h⟩ else none

@[simp] theorem readRegister_word (bound : registers ≤ 2^width) (register : Fin registers) :
    readRegister (registerWord bound register) = some register := by
  simp [readRegister, registerWord, register.isLt]

/-- Opcode and ordered operands; unused operand slots are omitted. -/
def fields (bound : registers ≤ 2^width) : Instruction width registers → Nat × List (Word width)
  | .constant dst value => (0, [registerWord bound dst, value])
  | .copy dst src => (1, [registerWord bound dst, registerWord bound src])
  | .add dst left right => (2, [registerWord bound dst, registerWord bound left, registerWord bound right])
  | .xor dst left right => (3, [registerWord bound dst, registerWord bound left, registerWord bound right])
  | .load dst address => (4, [registerWord bound dst, registerWord bound address])
  | .store address src => (5, [registerWord bound address, registerWord bound src])
  | .allocate src => (6, [registerWord bound src])
  | .release => (7, [])
  | .push src => (8, [registerWord bound src])
  | .pop dst => (9, [registerWord bound dst])
  | .emit src => (10, [registerWord bound src])
  | .branchZero src target => (11, [registerWord bound src, target])
  | .halt => (12, [])

def readFields (registers : Nat) (opcode : Nat) (operands : List (Word width)) :
    Option (Instruction width registers) :=
  match opcode, operands with
  | 0, [dst, value] => return .constant (← readRegister dst) value
  | 1, [dst, src] => return .copy (← readRegister dst) (← readRegister src)
  | 2, [dst, left, right] => return .add (← readRegister dst) (← readRegister left) (← readRegister right)
  | 3, [dst, left, right] => return .xor (← readRegister dst) (← readRegister left) (← readRegister right)
  | 4, [dst, address] => return .load (← readRegister dst) (← readRegister address)
  | 5, [address, src] => return .store (← readRegister address) (← readRegister src)
  | 6, [src] => return .allocate (← readRegister src)
  | 7, [] => some .release
  | 8, [src] => return .push (← readRegister src)
  | 9, [dst] => return .pop (← readRegister dst)
  | 10, [src] => return .emit (← readRegister src)
  | 11, [src, target] => return .branchZero (← readRegister src) target
  | 12, [] => some .halt
  | _, _ => none

theorem readFields_fields (bound : registers ≤ 2^width) (instruction : Instruction width registers) :
    readFields registers (fields bound instruction).1 (fields bound instruction).2 = some instruction := by
  cases instruction <;> simp [fields, readFields, readRegister_word, Bind.bind, Option.bind]

theorem fields_tag_lt (bound : registers ≤ 2^width) (instruction : Instruction width registers) :
    (fields bound instruction).1 < 2^4 := by
  cases instruction <;> simp [fields]

theorem fields_length_le (bound : registers ≤ 2^width) (instruction : Instruction width registers) :
    (fields bound instruction).2.length ≤ 3 := by
  cases instruction <;> simp [fields]

def encode (bound : registers ≤ 2^width) (instruction : Instruction width registers) : List Bool :=
  bits 4 (fields bound instruction).1 ++ encodeWords width (fields bound instruction).2

def read (width registers : Nat) (input : List Bool) : Option (Instruction width registers × List Bool) := do
  let opcode ← decodeWord 4 (input.take 4)
  let (operands, rest) ← readFramedWords width (input.drop 4)
  let instruction ← readFields registers opcode.val operands
  return (instruction, rest)

theorem read_encoded (bound : registers ≤ 2^width)
    (instruction : Instruction width registers) (suffix : List Bool) :
    read width registers (encode bound instruction ++ suffix) = some (instruction, suffix) := by
  have opcode := (wordEncoding 4).decode_encode
    (⟨(fields bound instruction).1, fields_tag_lt bound instruction⟩ : Word 4)
  change decodeWord 4 (bits 4 (fields bound instruction).1) = some _ at opcode
  simp only [encode, List.append_assoc, read]
  rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp),
    List.drop_append_of_le_length (by simp), List.drop_of_length_le (by simp)]
  rw [opcode]
  simp only [Bind.bind, Option.bind, List.nil_append]
  rw [readFramedWords_encoded]
  simp only [readFields_fields]
  rfl

def decode (width registers : Nat) (input : List Bool) : Option (Instruction width registers) := do
  let (instruction, rest) ← read width registers input
  if rest=[] then some instruction else none

def instructionEncoding (bound : registers ≤ 2^width) :
    Computability.Encoding (Instruction width registers) Bool where
  encode := encode bound
  decode := decode width registers
  decode_encode instruction := by
    have parsed := read_encoded bound instruction []
    simp only [List.append_nil] at parsed
    simp only [decode, parsed, Bind.bind, Option.bind]
    rfl

theorem encode_length (bound : registers ≤ 2^width) (instruction : Instruction width registers) :
    (encode bound instruction).length = 5 + (width+1)*(fields bound instruction).2.length := by
  simp only [encode, List.length_append, bits_length, encodeWords_length]
  omega

theorem encode_length_le (bound : registers ≤ 2^width) (instruction : Instruction width registers) :
    (encode bound instruction).length ≤ 3*width + 8 := by
  rw [encode_length]
  have boundLength := Nat.mul_le_mul_left (width+1) (fields_length_le bound instruction)
  omega

def readMany (width registers : Nat) : Nat → List Bool → Option (List (Instruction width registers) × List Bool)
  | 0, input => some ([], input)
  | count+1, input => do
    let (instruction, rest) ← read width registers input
    let (instructions, suffix) ← readMany width registers count rest
    return (instruction :: instructions, suffix)

def encodeMany (bound : registers ≤ 2^width) (instructions : List (Instruction width registers)) : List Bool :=
  instructions.flatMap (encode bound)

theorem readMany_encoded (bound : registers ≤ 2^width)
    (instructions : List (Instruction width registers)) (suffix : List Bool) :
    readMany width registers instructions.length (encodeMany bound instructions ++ suffix) =
      some (instructions, suffix) := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [encodeMany, List.flatMap_cons, List.length_cons, List.append_assoc, readMany]
    rw [read_encoded]
    simp only [Bind.bind, Option.bind]
    rw [show rest.flatMap (encode bound) = encodeMany bound rest from rfl, ih]
    rfl

theorem encodeMany_length_le (bound : registers ≤ 2^width)
    (instructions : List (Instruction width registers)) :
    (encodeMany bound instructions).length ≤ (3*width+8)*instructions.length := by
  induction instructions with
  | nil => simp [encodeMany]
  | cons instruction rest ih =>
    simp only [encodeMany, List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
    simpa only [encodeMany, Nat.add_comm] using Nat.add_le_add (encode_length_le bound instruction) ih

def encodeProgram (bound : registers ≤ 2^width) (program : Program width registers) : List Bool :=
  frameCount program.size (encodeMany bound program.toList)

def decodeProgram (width registers : Nat) (input : List Bool) : Option (Program width registers) := do
  let (count, payload) ← readCount input
  let (instructions, rest) ← readMany width registers count payload
  if rest=[] then some instructions.toArray else none

theorem decode_encodeProgram (bound : registers ≤ 2^width) (program : Program width registers) :
    decodeProgram width registers (encodeProgram bound program) = some program := by
  simp only [encodeProgram, decodeProgram, readCount_frame, Bind.bind, Option.bind]
  have parsed := readMany_encoded bound program.toList []
  simp only [List.append_nil, Array.length_toList] at parsed
  rw [parsed]
  simp only [Array.toArray_toList]
  rfl

def programEncoding (bound : registers ≤ 2^width) : Computability.Encoding (Program width registers) Bool where
  encode := encodeProgram bound
  decode := decodeProgram width registers
  decode_encode := decode_encodeProgram bound

theorem encodeProgram_length_le (bound : registers ≤ 2^width) (program : Program width registers) :
    (encodeProgram bound program).length ≤ (3*width+9)*program.size+1 := by
  have payloadBound := encodeMany_length_le bound program.toList
  simp only [Array.length_toList] at payloadBound
  simp only [encodeProgram, frameCount, List.length_append, List.length_replicate, List.length_cons]
  calc
    _ ≤ program.size + ((3*width+8)*program.size+1) := Nat.add_le_add_left (Nat.add_le_add_right payloadBound 1) _
    _ = _ := by simp only [Nat.add_mul]; omega

end Controller.Complexity.InstructionCodec
