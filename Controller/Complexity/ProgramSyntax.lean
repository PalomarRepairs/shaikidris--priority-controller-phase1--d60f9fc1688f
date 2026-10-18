module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.InstructionFrontend

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Successful native instruction and program-prefix decoding reconstructs
the exact consumed bytes. The source suffix is retained by each inverse law. -/
namespace Controller.Complexity.ProgramSyntax

theorem register_inverse (bound : registers ≤ 2^width) (word : Controller.Cost.Word width) (index : Fin registers)
    (decoded : InstructionCodec.readRegister word=some index) : InstructionCodec.registerWord bound index=word := by
  unfold InstructionCodec.readRegister at decoded
  split at decoded
  next valid =>
    simp only [Option.some.injEq] at decoded
    apply Fin.ext
    exact (congrArg Fin.val decoded).symm
  next invalid => simp at decoded

theorem fields_inverse (bound : registers ≤ 2^width) (opcode : Fin 16) (words : List (Controller.Cost.Word width))
    (instruction : Controller.Cost.Instruction width registers)
    (decoded : InstructionCodec.readFields registers opcode.val words=some instruction) :
    InstructionCodec.fields bound instruction=(opcode.val,words) := by
  fin_cases opcode <;>
    rcases words with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,rest⟩⟩⟩⟩ <;>
    simp only [InstructionCodec.readFields, Bind.bind, Option.bind] at decoded
  all_goals
    try simp only [InstructionCodec.readRegister] at decoded
    try split_ifs at decoded
    all_goals simp_all [InstructionCodec.fields, InstructionCodec.registerWord]
    all_goals cases decoded; rfl

theorem read_inverse (bound : registers ≤ 2^width) (input : List Bool)
    (instruction : Controller.Cost.Instruction width registers) (suffix : List Bool)
    (decoded : InstructionCodec.read width registers input=some (instruction,suffix)) :
    input=InstructionCodec.encode bound instruction++suffix := by
  obtain ⟨opcode,words,parsed,native⟩ := InstructionFrontend.read_parts width registers input instruction suffix decoded
  have canonical := InstructionFrontend.syntax_sound width input opcode words suffix parsed
  have fields := fields_inverse bound opcode words instruction native
  simpa only [InstructionCodec.encode, fields, List.append_assoc] using canonical

theorem readMany_inverse (bound : registers ≤ 2^width) (count : Nat) (input : List Bool)
    (instructions : List (Controller.Cost.Instruction width registers)) (suffix : List Bool)
    (decoded : InstructionCodec.readMany width registers count input=some (instructions,suffix)) :
    instructions.length=count ∧ input=InstructionCodec.encodeMany bound instructions++suffix := by
  induction count generalizing input instructions with
  | zero =>
    simp only [InstructionCodec.readMany, Option.some.injEq, Prod.mk.injEq] at decoded
    obtain ⟨rfl,rfl⟩ := decoded
    exact ⟨rfl,rfl⟩
  | succ count ih =>
    cases firstRead : InstructionCodec.read width registers input with
    | none => simp [InstructionCodec.readMany, firstRead] at decoded
    | some pair =>
      rcases pair with ⟨instruction,rest⟩
      cases tailRead : InstructionCodec.readMany width registers count rest with
      | none => simp [InstructionCodec.readMany, firstRead, tailRead] at decoded
      | some tail =>
        rcases tail with ⟨values,remaining⟩
        simp only [InstructionCodec.readMany, firstRead, tailRead, Bind.bind, Option.bind, Option.pure_def,
          Option.some.injEq, Prod.mk.injEq] at decoded
        obtain ⟨rfl,rfl⟩ := decoded
        obtain ⟨length,bytes⟩ := ih _ _ tailRead
        have firstBytes := read_inverse bound input instruction rest firstRead
        refine ⟨by simp [length],?_⟩
        rw [firstBytes, bytes]
        simp only [InstructionCodec.encodeMany, List.flatMap_cons, List.append_assoc]

def readPrefix (width registers : Nat) (input : List Bool) :
    Option (List (Controller.Cost.Instruction width registers) × List Bool) := do
  let (count,payload) ← Encoding.readCount input
  InstructionCodec.readMany width registers count payload

theorem prefix_inverse (bound : registers ≤ 2^width) (input : List Bool)
    (instructions : List (Controller.Cost.Instruction width registers)) (suffix : List Bool)
    (decoded : readPrefix width registers input=some (instructions,suffix)) :
    input=Encoding.frameCount instructions.length (InstructionCodec.encodeMany bound instructions++suffix) := by
  cases header : Encoding.readCount input with
  | none => simp [readPrefix, header] at decoded
  | some pair =>
    rcases pair with ⟨count,payload⟩
    have parsed : InstructionCodec.readMany width registers count payload=some (instructions,suffix) := by
      simpa only [readPrefix, header, Bind.bind, Option.bind] using decoded
    obtain ⟨length,body⟩ := readMany_inverse bound count payload instructions suffix parsed
    rw [HeaderParser.readCount_sound header, body, ← length]

end Controller.Complexity.ProgramSyntax
