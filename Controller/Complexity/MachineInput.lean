module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.MachineBridge

@[expose] public section

/-! A self-describing binary input carries the word width, register count,
program and full initial RAM state. Global counts use unary delimiters;
instruction operands and stored machine words retain their exact binary width. -/
namespace Controller.Complexity.MachineInput
open Controller.Cost Encoding

structure Image where
  width : Nat
  registers : Nat
  registerBound : registers ≤ 2^width
  program : Program width registers
  state : State width registers

def envelope (width registers : Nat) (payload : List Bool) : List Bool :=
  frameCount width (frameCount registers payload)

def encode (image : Image) : List Bool :=
  envelope image.width image.registers
    (InstructionCodec.encodeProgram image.registerBound image.program ++ MachineBridge.encodeState image.state)

def decode (input : List Bool) : Option Image := do
  let (width,rest) ← readCount input
  let (registers,rest) ← readCount rest
  if bound : registers ≤ 2^width then
    let (count,rest) ← readCount rest
    let (instructions,rest) ← InstructionCodec.readMany width registers count rest
    let state ← MachineBridge.decodeState width registers rest
    return ⟨width,registers,bound,instructions.toArray,state⟩
  else none

theorem decode_encode (image : Image) : decode (encode image) = some image := by
  rcases image with ⟨width,registers,bound,program,state⟩
  simp only [encode, envelope, decode, readCount_frame, Bind.bind, Option.bind, dite_eq_left bound]
  have framing : InstructionCodec.encodeProgram bound program ++ MachineBridge.encodeState state =
      frameCount program.size (InstructionCodec.encodeMany bound program.toList ++ MachineBridge.encodeState state) := by
    simp only [InstructionCodec.encodeProgram, frameCount, List.append_assoc, List.cons_append]
  rw [framing, readCount_frame]
  dsimp only
  have parsed := InstructionCodec.readMany_encoded bound program.toList (MachineBridge.encodeState state)
  simp only [Array.length_toList] at parsed
  rw [parsed]
  dsimp only
  simp only [MachineBridge.decode_encode, Array.toArray_toList]
  rfl

def encoding : Computability.Encoding Image Bool where
  encode := encode
  decode := decode
  decode_encode := decode_encode

theorem encode_injective : Function.Injective encode := encoding.encode_injective

theorem envelope_length (width registers : Nat) (payload : List Bool) :
    (envelope width registers payload).length = width+registers+payload.length+2 := by
  simp only [envelope, frameCount, List.length_append, List.length_replicate, List.length_cons]
  omega

theorem encode_length_le (image : Image) :
    (encode image).length ≤ image.width+image.registers+
      (3*image.width+9)*image.program.size+(image.width+1)*image.state.liveWords+9 := by
  have programBound := InstructionCodec.encodeProgram_length_le image.registerBound image.program
  simp only [encode, envelope_length, List.length_append, MachineBridge.encodeState_length]
  omega

end Controller.Complexity.MachineInput
