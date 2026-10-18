module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroAdmissibleCaller
public import Controller.Horn.NormalizeCode
public import Controller.Cost.CompilerArrayTrace

@[expose] public section

/-! Resident per-occurrence blocks use the actual source-addressed constructor
and fixed-size backend kernels. All jump destinations are computed from their
placement. Source field formation and encoded backing-cell writes are separate
from the instruction-list assembly and size results below. -/
namespace Controller.Cost.ForestZeroResident
open Controller.Cost Controller.Cost.GateProgram
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroCompile
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroDictionary

/-- Source reads have fixed shape; relocation changes operands but no lengths. -/
theorem emit_length_relocate (width first second : Nat) (references : List (Reference ambient)) :
    (emitCode width first references).length = (emitCode width second references).length := by
  induction references generalizing first second with
  | nil => rfl
  | cons reference rest ih =>
      simp only [emitCode, List.length_append, literalCode_length]
      simpa only [literalCode_length] using congrArg (fun length : Nat => (readCode width reference).length + 23 + length)
        (ih (first + (literalCode width first reference).length)
          (second + (literalCode width second reference).length))

theorem constructor_length_relocate (width first second protectedEnd recordHeader endHeader
    firstReturn secondReturn : Nat) (references : List (List (Reference ambient))) :
    (constructorCode width first protectedEnd recordHeader endHeader firstReturn references).length =
      (constructorCode width second protectedEnd recordHeader endHeader secondReturn references).length := by
  simp only [constructorCode, ForestZeroQueryCaller.queryCode, ForestZeroQueryCaller.countCode_length,
    List.length_append, code_length, ForestZeroQueryCaller.preservingHeaderCode_length,
    ForestZeroAssembly.assemblyCode, List.length_cons, List.length_nil,
    ForestZeroDirectory.code_length]
  have relocated := emit_length_relocate width
    (first + 12 + 2 + 5 * (ForestZeroAssembly.originalRows (reservedReferences references)).length)
    (second + 12 + 2 + 5 * (ForestZeroAssembly.originalRows (reservedReferences references)).length)
    (reservedReferences references).flatten
  omega


structure Placement where
  source : Nat
  constructor : Nat
  query : Nat
  scan : Nat
  seedDone : Nat
  fetch : Nat
  advance : Nat
  bucket : Nat
  ready : Nat
  success : Nat
  conflict : Nat
  projection : Nat
  cleanup : Nat
  returned : Nat
  dispatch : Nat
  next : Nat

/-- Declared positions get distinct blocks even when their root identifiers agree. -/
def placement (width protectedEnd sourceEntry nextEntry : Nat)
    (references : List (List (Reference ambient))) : Placement :=
  let constructor := sourceEntry + 15
  let query := constructor + (constructorCode width constructor protectedEnd protectedEnd (protectedEnd + 4) 0 references).length
  { source := sourceEntry, constructor := constructor, query := query,
    scan := query + 261, seedDone := query + 308, fetch := query + 312,
    advance := query + 326, bucket := query + 331, ready := query + 343,
    success := query + 369, conflict := query + 382, projection := query + 395,
    cleanup := query + 430, returned := query + 437, dispatch := query + 465, next := nextEntry }

def widen (code : Code width) : Program width 8 :=
  (code.map RegisterWiden.widenInstruction).toArray

@[simp] private theorem widen_size (code : Code width) : (widen code).size = code.length := by
  simp [widen]

/-- Every block is an existing complete kernel, not an unrolled local-count or
ambient-channel loop. The source occurrence constructor is the sole variable block. -/
def chunks (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient)
    (sourceEntry nextEntry : Nat) : List (Program width 8) :=
  let p := placement width heap.size sourceEntry nextEntry references
  let dictionary := constructorDictionary heap layout (empty ambient) references
  let formula := constructorFormula heap layout (empty ambient) (empty_coherent ambient) references channels within
  let backend := constructorFormulaBackend heap layout (empty ambient) (empty_coherent ambient) references channels within
  let base := (constructorHeap heap layout (empty ambient) references channels).size
  let recordStart := base + 5 * dictionary.coordinates.size + 4
  [reuseEntryCode width,
   widen (keepCode width),
   #[.constant 0 (word width (heap.size + 5 + 2 * (references.length + 1)))],
   widen (constructorCode width p.constructor heap.size heap.size (heap.size + 4) p.query references),
   scratchCountCode width,
   Controller.Horn.TrackedAllocate.code width (p.query + 11),
   scratchHeaderCode width,
   scratchEndpointCode,
   saveProjectionCode,
   Controller.Horn.NormalizeCNF.code width (p.query + 42) dictionary.coordinates.size backend.base
     backend.recordHeader backend.inputHeader backend.firstHeader backend.directoryHeader backend.endHeader,
   ForestZeroHeaderBridge.saveCode width heap.size,
   Controller.Horn.IndexScan.code (n := dictionary.coordinates.size) width base recordStart (p.query + 210),
   ForestZeroHeaderBridge.restoreCode width,
   ForestZeroReclaim.captureCode width,
   ForestZeroSeedSetup.code (n := dictionary.coordinates.size) width base heap.size recordStart p.scan,
   Controller.Horn.WorklistSeed.code (n := dictionary.coordinates.size) width base p.scan p.seedDone p.conflict,
   Controller.Horn.WorklistAccept.headSetupCode (n := dictionary.coordinates.size) width base p.fetch,
   Controller.Horn.WorklistFIFO.fetchCode (n := dictionary.coordinates.size) width base p.fetch p.success p.bucket,
   Controller.Horn.WorklistFIFO.advanceCode (n := dictionary.coordinates.size) width base p.fetch,
   Controller.Horn.WorklistBucketLoop.code width p.bucket p.advance p.ready,
   Controller.Horn.WorklistBucketReady.code (n := dictionary.coordinates.size) width base p.ready p.advance p.conflict p.bucket,
   ForestZeroAnswer.savedCode width 1 p.projection,
   ForestZeroAnswer.savedCode width 0 p.cleanup,
   projectionConstantsCode width,
   channelPrepareCode width,
   ForestZeroChannelEmit.code width (p.projection + 21) p.cleanup,
   ForestZeroReclaim.setupCode width,
   ForestZeroReclaim.code width (p.cleanup + 3) p.returned,
   widen ((resetPrepareCode width).toList),
   widen (ForestZeroReset.code width (p.returned + 15)),
   #[.pop 4],
   ForestZeroRootLoop.dispatchCode width nextEntry]

def instructions (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient)
    (sourceEntry nextEntry : Nat) : List (Instruction width 8) :=
  (chunks heap layout references channels within sourceEntry nextEntry).flatMap Array.toList

private theorem residentEntry_size (width : Nat) : (reuseEntryCode width).size = 3 := by rfl
private theorem residentProjection_size (width : Nat) : (projectionConstantsCode width).size = 2 := by rfl
private theorem residentHeaderSave_size (width header : Nat) : (ForestZeroHeaderBridge.saveCode width header).size = 7 := by rfl
private theorem residentHeaderRestore_size (width : Nat) : (ForestZeroHeaderBridge.restoreCode width).size = 3 := by rfl
private theorem residentCapture_size (width : Nat) : (ForestZeroReclaim.captureCode width).size = 6 := by rfl
private theorem residentSeedSetup_size (width n base header records scan : Nat) : (ForestZeroSeedSetup.code (n := n) width base header records scan).size = 10 := by rfl
private theorem residentSavedAnswer_size (width value returnPC : Nat) : (ForestZeroAnswer.savedCode width value returnPC).size = 13 := by rfl
private theorem residentCleanupSetup_size (width : Nat) : (ForestZeroReclaim.setupCode width).size = 3 := by rfl
private theorem residentCleanupLoop_size (width entry exit : Nat) : (ForestZeroReclaim.code width entry exit).size = 4 := by rfl
private theorem residentResetPrepare_size (width : Nat) : (resetPrepareCode width).size = 15 := by rfl
private theorem residentResetLoop_size (width entry : Nat) : (ForestZeroReset.code width entry).length = 12 := by rfl
private theorem residentDispatch_size (width nextEntry : Nat) : (ForestZeroRootLoop.dispatchCode width nextEntry).size = 2 := by rfl
private theorem resident_constructor_position (width protectedEnd sourceEntry nextEntry : Nat)
    (references : List (List (Reference ambient))) :
    (placement width protectedEnd sourceEntry nextEntry references).constructor = sourceEntry + 15 := rfl

/-- Kernel instruction counts are independent of channel and local counts. -/
theorem chunk_sizes (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient)
    (sourceEntry nextEntry : Nat) :
    (chunks heap layout references channels within sourceEntry nextEntry).map Array.size =
      [3, 11, 1,
       (constructorCode width (sourceEntry + 15) heap.size heap.size (heap.size + 4)
         (placement width heap.size sourceEntry nextEntry references).query references).length,
       11, 5, 15, 5, 6, 161, 7, 32, 3, 6, 10, 47, 4, 14, 5, 12, 26,
       13, 13, 2, 19, 14, 3, 4, 15, 12, 1, 2] := by
  simp only [chunks, List.map_cons, List.map_nil, widen_size,
    resident_constructor_position, residentEntry_size, keepCode_length,
    scratchCountCode_size, Controller.Horn.TrackedAllocate.code_size,
    scratchHeaderCode_size, scratchEndpointCode_size, saveProjectionCode_size,
    Controller.Horn.NormalizeCNF.code_size, residentHeaderSave_size,
    Controller.Horn.IndexScan.code_size, residentHeaderRestore_size, residentCapture_size,
    residentSeedSetup_size, Controller.Horn.WorklistSeed.code_size,
    Controller.Horn.WorklistAccept.head_setup_size, Controller.Horn.WorklistFIFO.fetch_size,
    Controller.Horn.WorklistFIFO.advance_size, Controller.Horn.WorklistBucketLoop.code_size,
    Controller.Horn.WorklistBucketReady.code_size, residentSavedAnswer_size,
    residentProjection_size, channelPrepareCode_size, ForestZeroChannelEmit.code_size,
    residentCleanupSetup_size, residentCleanupLoop_size, Array.length_toList,
    residentResetPrepare_size, residentResetLoop_size, residentDispatch_size]
  rfl

theorem instruction_length (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient)
    (sourceEntry nextEntry : Nat) :
    (instructions heap layout references channels within sourceEntry nextEntry).length ≤
      584 + 5 * references.length + 28 * references.flatten.length := by
  have sizes := chunk_sizes heap layout references channels within sourceEntry nextEntry
  simp only [instructions, List.length_flatMap, Array.length_toList, Function.comp_def]
  have constructorBound := constructorCode_length width (sourceEntry + 15) heap.size heap.size
    (heap.size + 4) (placement width heap.size sourceEntry nextEntry references).query references
  change ((chunks heap layout references channels within sourceEntry nextEntry).map Array.size).sum ≤ _
  rw [sizes]
  simp only [List.sum_cons, List.sum_nil]
  omega

/-- Materialization appends by one actual array push for each instruction. -/
def materialize (priorProgram : Program width 8) (items : List (Instruction width 8)) : Program width 8 :=
  items.toArrayAux priorProgram

theorem materialize_trace (priorProgram : Program width 8) (items : List (Instruction width 8)) :
    CompilerArrayTrace.Trace items priorProgram (materialize priorProgram items) items.length :=
  CompilerArrayTrace.exists_trace items priorProgram

theorem materialize_contents (priorProgram : Program width 8) (items : List (Instruction width 8)) :
    (materialize priorProgram items).toList = priorProgram.toList ++ items :=
  (CompilerArrayTrace.exact_trace (materialize_trace priorProgram items)).2.2

theorem materialize_size (priorProgram : Program width 8) (items : List (Instruction width 8)) :
    (materialize priorProgram items).size = priorProgram.size + items.length :=
  CompilerArrayTrace.final_size (materialize_trace priorProgram items)

/-- A resident block is fetched from its actual placement in the pushed array. -/
theorem materialize_block (priorProgram : Program width 8) (before block after : List (Instruction width 8))
    (index : Nat) (within : index < block.length) :
    (materialize priorProgram (before ++ block ++ after))[priorProgram.size + before.length + index]? = block[index]? := by
  have contents := materialize_contents priorProgram (before ++ block ++ after)
  have getter := congrArg (fun values : List (Instruction width 8) =>
    values[priorProgram.size + before.length + index]?) contents
  simp only [Array.getElem?_toList, List.append_assoc] at getter
  simp only [List.append_assoc]
  rw [getter]
  rw [List.getElem?_append_right (by simp only [Array.length_toList]; omega)]
  simp only [Array.length_toList]
  have first : priorProgram.size + before.length + index - priorProgram.size = before.length + index := by omega
  rw [first, List.getElem?_append_right (by omega)]
  have second : before.length + index - before.length = index := by omega
  rw [second, List.getElem?_append_left within]

/-- The complete resident array retains any preceding program segment. -/
def program (priorProgram : Program width 8) (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient)
    (nextEntry : Nat) : Program width 8 :=
  materialize priorProgram (instructions heap layout references channels within priorProgram.size nextEntry)

/-- One opcode and three padded operands are formed explicitly. Register
identifiers are converted to words; existing literal words are copied. -/
def instructionFields (instruction : Instruction width registers) : List (Word width) :=
  match instruction with
  | .constant dst value => [word width 0, word width dst.val, value, word width 0]
  | .copy dst src => [word width 1, word width dst.val, word width src.val, word width 0]
  | .add dst left right => [word width 2, word width dst.val, word width left.val, word width right.val]
  | .xor dst left right => [word width 3, word width dst.val, word width left.val, word width right.val]
  | .load dst address => [word width 4, word width dst.val, word width address.val, word width 0]
  | .store address src => [word width 5, word width address.val, word width src.val, word width 0]
  | .allocate src => [word width 6, word width src.val, word width 0, word width 0]
  | .release => [word width 7, word width 0, word width 0, word width 0]
  | .push src => [word width 8, word width src.val, word width 0, word width 0]
  | .pop dst => [word width 9, word width dst.val, word width 0, word width 0]
  | .emit src => [word width 10, word width src.val, word width 0, word width 0]
  | .branchZero src target => [word width 11, word width src.val, target, word width 0]
  | .halt => [word width 12, word width 0, word width 0, word width 0]

@[simp] theorem instructionFields_length (instruction : Instruction width registers) :
    (instructionFields instruction).length = 4 := by cases instruction <;> rfl

/-- Primitive field construction distinguishes forming an encoded natural
from copying an already represented operand word. -/
inductive FieldInput (width : Nat) where
  | natural (value : Nat)
  | existing (value : Word width)

def FieldInput.value : FieldInput width → Word width
  | .natural number => word width number
  | .existing stored => stored

def instructionInputs (instruction : Instruction width registers) : List (FieldInput width) :=
  match instruction with
  | .constant dst value => [.natural 0, .natural dst.val, .existing value, .natural 0]
  | .copy dst src => [.natural 1, .natural dst.val, .natural src.val, .natural 0]
  | .add dst left right => [.natural 2, .natural dst.val, .natural left.val, .natural right.val]
  | .xor dst left right => [.natural 3, .natural dst.val, .natural left.val, .natural right.val]
  | .load dst address => [.natural 4, .natural dst.val, .natural address.val, .natural 0]
  | .store address src => [.natural 5, .natural address.val, .natural src.val, .natural 0]
  | .allocate src => [.natural 6, .natural src.val, .natural 0, .natural 0]
  | .release => [.natural 7, .natural 0, .natural 0, .natural 0]
  | .push src => [.natural 8, .natural src.val, .natural 0, .natural 0]
  | .pop dst => [.natural 9, .natural dst.val, .natural 0, .natural 0]
  | .emit src => [.natural 10, .natural src.val, .natural 0, .natural 0]
  | .branchZero src target => [.natural 11, .natural src.val, .existing target, .natural 0]
  | .halt => [.natural 12, .natural 0, .natural 0, .natural 0]

inductive FormationTrace : List (FieldInput width) → List (Word width) → Nat → Prop
  | nil : FormationTrace [] [] 0
  | natural (number rest fields count) (next : FormationTrace rest fields count) :
      FormationTrace (.natural number :: rest) (word width number :: fields) (count + 1)
  | existing (value rest fields count) (next : FormationTrace rest fields count) :
      FormationTrace (.existing value :: rest) (value :: fields) (count + 1)

theorem formation_trace (inputs : List (FieldInput width)) :
    FormationTrace inputs (inputs.map FieldInput.value) inputs.length := by
  induction inputs with
  | nil => exact FormationTrace.nil
  | cons input rest ih =>
      cases input with
      | natural number => exact FormationTrace.natural number rest _ _ ih
      | existing value => exact FormationTrace.existing value rest _ _ ih

theorem instruction_formation (instruction : Instruction width registers) :
    FormationTrace (instructionInputs instruction) (instructionFields instruction) 4 := by
  have trace := formation_trace (instructionInputs instruction)
  cases instruction <;> exact trace

/-- Every field is formed or copied once, and each resulting backing word is
pushed once. This construction count is distinct from fetched program ticks. -/
inductive BackingTrace : List (Instruction width registers) → Array (Word width) →
    Array (Word width) → Nat → Nat → Prop
  | nil (initial) : BackingTrace [] initial initial 0 0
  | cons (instruction rest initial next final formed written)
      (formation : FormationTrace (instructionInputs instruction) (instructionFields instruction) 4)
      (fields : CompilerArrayTrace.Trace (instructionFields instruction) initial next 4)
      (remaining : BackingTrace rest next final formed written) :
      BackingTrace (instruction :: rest) initial final (formed + 4) (written + 4)

def backing : List (Instruction width registers) → Array (Word width) → Array (Word width)
  | [], initial => initial
  | instruction :: rest, initial =>
      backing rest ((instructionFields instruction).toArrayAux initial)

theorem backing_trace (instructions : List (Instruction width registers)) (initial : Array (Word width)) :
    BackingTrace instructions initial (backing instructions initial)
      (4 * instructions.length) (4 * instructions.length) := by
  induction instructions generalizing initial with
  | nil => exact BackingTrace.nil initial
  | cons instruction rest ih =>
      have fields := CompilerArrayTrace.exists_trace (instructionFields instruction) initial
      rw [instructionFields_length] at fields
      have trace := BackingTrace.cons instruction rest initial _ _ _ _ (instruction_formation instruction) fields
        (ih ((instructionFields instruction).toArrayAux initial))
      simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, backing] using trace

theorem backing_contents {items : List (Instruction width registers)}
    (trace : BackingTrace items initial final formed written) :
    final.toList = initial.toList ++ items.flatMap instructionFields ∧
    formed = 4 * items.length ∧ written = 4 * items.length := by
  induction trace with
  | nil initial => simp
  | cons instruction rest initial next final formed written formation fields remaining ih =>
      have fieldsContents := (CompilerArrayTrace.exact_trace fields).2.2
      refine ⟨?_, ?_, ?_⟩
      · rw [ih.1, fieldsContents]
        simp only [List.flatMap_cons, List.append_assoc]
      · rw [ih.2.1]; simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      · rw [ih.2.2]; simp only [List.length_cons, Nat.mul_add, Nat.mul_one]

theorem backing_size {items : List (Instruction width registers)}
    (trace : BackingTrace items initial final formed written) :
    final.size = initial.size + written := by
  have contents := congrArg List.length (backing_contents trace).1
  simp only [Array.length_toList, List.length_append, List.length_flatMap,
    instructionFields_length, List.map_const, List.sum_replicate] at contents
  have total : (items.map fun _ => (4 : Nat)).sum = 4 * items.length := by
    clear trace contents
    induction items with
    | nil => rfl
    | cons item rest ih =>
        change 4 + (rest.map fun _ => (4 : Nat)).sum = 4 * (rest.length + 1)
        rw [ih]
        omega
  rw [total] at contents
  rw [(backing_contents trace).2.2]
  omega

-- These are construction operations, not fetched RAM ticks. A lossless
-- representation theorem also checks opcode and register identifiers fit the
-- selected width before using these fields as a physical instruction encoding.

/-- The lossless numeric fields before packing words. -/
def numericFields (instruction : Instruction width registers) : List Nat :=
  match instruction with
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

theorem instructionFields_exact (instruction : Instruction width registers)
    (registersFit : registers ≤ 2 ^ width) (opcodesFit : 13 ≤ 2 ^ width) :
    (instructionFields instruction).map Fin.val = numericFields instruction := by
  have registerValue (register : Fin registers) : (word width register.val).val = register.val :=
    Nat.mod_eq_of_lt (register.isLt.trans_le registersFit)
  have opcodeValue (opcode : Nat) (small : opcode < 13) : (word width opcode).val = opcode :=
    Nat.mod_eq_of_lt (small.trans_le opcodesFit)
  cases instruction <;>
    simp only [instructionFields, numericFields, List.map_cons, List.map_nil,
      registerValue, opcodeValue 0 (by decide), opcodeValue 1 (by decide), opcodeValue 2 (by decide), opcodeValue 3 (by decide), opcodeValue 4 (by decide), opcodeValue 5 (by decide), opcodeValue 6 (by decide), opcodeValue 7 (by decide), opcodeValue 8 (by decide), opcodeValue 9 (by decide), opcodeValue 10 (by decide), opcodeValue 11 (by decide), opcodeValue 12 (by decide)]

end Controller.Cost.ForestZeroResident
