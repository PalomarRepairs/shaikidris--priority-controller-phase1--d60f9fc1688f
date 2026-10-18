module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationCounter
public import Controller.Cost.EnumerationPrefixOracle

@[expose] public section

/-! The immutable complete/seek enumeration instruction array. Runtime state
uses the retained packet, one 2n-word prefix region, depth in register three,
mode in register five and the shared oracle answer in register four. -/
namespace Controller.Cost.EnumerationDriverCode
open Controller.Decoder Controller.Native Controller.Cost.GateProgram

structure Labels where
  start : Nat
  call : Nat
  restore : Nat
  dispatch : Nat
  seekPost : Nat
  seekFail : Nat
  initialPost : Nat
  completePost : Nat
  completeRepair : Nat
  descend : Nat
  forcedDescend : Nat
  seek : Nat
  seekForced : Nat
  seekTry : Nat
  emit : Nat
  halt : Nat
  oracle : Nat

def emitLength (parameters : Parameters) (graph : DAG parameters.channels) (width : Nat) : Nat :=
  (EnumerationCanonicalEmit.code parameters width 0 (SharedDetectorPrepared.packetSize graph)).length

def labels (parameters : Parameters) (graph : DAG parameters.channels) (width entry : Nat) : Labels :=
  let call := entry + 4 * parameters.channels + 6
  let restore := call + 22
  let dispatch := restore + 4 * parameters.channels + 2
  let seekPost := dispatch + 6
  let seekFail := seekPost + 5
  let initialPost := seekFail + 6
  let completePost := initialPost + 3
  let completeRepair := completePost + 5
  let descend := completeRepair + 12
  let forcedDescend := descend + 10 + (if parameters.buses = 1 then 3 else 0)
  let seek := forcedDescend + 4
  let seekForced := seek + 19 + (if parameters.buses = 1 then 3 else 0)
  let seekTry := seekForced + 6
  let emit := seekTry + 11
  let halt := emit + emitLength parameters graph width + 2
  { start := entry, call, restore, dispatch, seekPost, seekFail, initialPost, completePost,
    completeRepair, descend, forcedDescend, seek, seekForced, seekTry, emit, halt, oracle := halt + 1 }

def jump (width target : Nat) : List (Instruction width 8) :=
  [.constant 0 (word width 0), .branchZero 0 (word width target)]

def initWords (parameters : Parameters) (width : Nat) : List (Word width) :=
  EnumerationPrefixOracle.masks parameters width ∅ ∅

def allocateWords (words : List (Word width)) : List (Instruction width 8) :=
  words.flatMap (fun value => [.constant 0 value, .allocate 0])

@[simp] theorem allocateWords_length (words : List (Word width)) :
    (allocateWords words).length = 2 * words.length := by
  induction words with
  | nil => simp [allocateWords]
  | cons value rest ih => simp [allocateWords, Nat.mul_succ]; omega

private theorem emit_length_entry (parameters : Parameters) (width entry first base : Nat) :
    (EnumerationCanonicalEmit.code parameters width entry base).length =
      (EnumerationCanonicalEmit.code parameters width first base).length := by
  simp only [EnumerationCanonicalEmit.code, List.length_append, EnumerationCanonicalEmit.header_length,
    EnumerationEmissionOperands.code_length]

def readBit (width base : Nat) : List (Instruction width 8) :=
  [.constant 0 (word width base), .add 0 0 3, .load 1 0]

def chunks (parameters : Parameters) (graph : DAG parameters.channels) (width entry : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) : List (List (Instruction width 8)) :=
  let l := labels parameters graph width entry
  let b := SharedDetectorPrepared.packetSize graph
  let f := b + parameters.channels
  let inc := EnumerationCounter.code width 1
  let dec := EnumerationCounter.code width (2 ^ width - 1)
  let test (register : Fin 8) (value done : Nat) := (SharedTagCompare.code width done value register).toList
  let write (base : Nat) (value : Bool) := EnumerationMaskWrite.code width base value
  [ -- Initial feasibility test, also handling drive=false without entering the oracle.
    [.constant 0 (word width (if parameters.drive then 1 else 0)), .branchZero 0 (word width l.halt)] ++
      allocateWords (initWords parameters width) ++ [.constant 3 (word width 0), .constant 5 (word width 0)] ++ jump width l.call,
    EnumerationPrefixOracle.callCode parameters graph width l.call l.oracle,
    EnumerationPrefixReturn.code width (2 * parameters.channels),
    test 5 0 l.initialPost ++ test 5 1 l.completePost,
    [.branchZero 4 (word width l.seekFail)] ++ inc ++ jump width l.descend,
    write b false ++ jump width l.seek,
    [.branchZero 4 (word width l.halt)] ++ jump width l.descend,
    [.branchZero 4 (word width l.completeRepair)] ++ inc ++ jump width l.descend,
    write f false ++ write b true ++ inc ++ jump width l.descend,
    test 3 parameters.channels l.emit ++
      (if parameters.buses = 1 then test 3 parameters.bridge.target.val l.forcedDescend else []) ++
      write f true ++ [.constant 5 (word width 1)] ++ jump width l.call,
    inc ++ jump width l.descend,
    test 3 0 l.halt ++ dec ++ readBit width b ++ [.branchZero 1 (word width l.seekTry)] ++
      (if parameters.buses = 1 then test 3 parameters.bridge.target.val l.seekForced else []) ++
      write b false ++ write f false ++ jump width l.seek,
    write f false ++ jump width l.seek,
    write b true ++ write f false ++ [.constant 5 (word width 2)] ++ jump width l.call,
    EnumerationCanonicalEmit.code parameters width l.emit b ++ jump width l.seek,
    [.halt],
    EnumerationPrefixOracle.oracleCode parameters graph width rows roots l.oracle l.restore ]

def code (parameters : Parameters) (graph : DAG parameters.channels) (width entry : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) : List (Instruction width 8) :=
  (chunks parameters graph width entry rows roots).flatten

theorem chunks_lengths (parameters : Parameters) (graph : DAG parameters.channels) (width entry : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) :
    (chunks parameters graph width entry rows roots).map List.length =
      [4 * parameters.channels + 6, 22, 4 * parameters.channels + 2, 6, 5, 6, 3, 5, 12,
       10 + (if parameters.buses = 1 then 3 else 0), 4,
       19 + (if parameters.buses = 1 then 3 else 0), 6, 11,
       emitLength parameters graph width + 2, 1,
       (EnumerationPrefixOracle.oracleCode parameters graph width rows roots
         (labels parameters graph width entry).oracle (labels parameters graph width entry).restore).length] := by
  by_cases one : parameters.buses = 1
  all_goals
    simp [chunks, one, jump, readBit, initWords, EnumerationPrefixOracle.callCode,
      EnumerationCounter.code_length, EnumerationMaskWrite.code_length,
      emit_length_entry parameters width (labels parameters graph width entry).emit 0,
      emitLength, Nat.add_assoc]
    omega


theorem code_length_bound (parameters : Parameters) (graph : DAG parameters.channels) (width entry : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (matched : ForestIndexedOperands.RootsMatch graph roots) :
    (code parameters graph width entry rows roots).length ≤
      8 * parameters.channels + 129 + 6 * EnumerationCanonicalEmit.Coordinates parameters +
        (610 * (graph.countedSize + 1) + 1609) := by
  have total : (code parameters graph width entry rows roots).length =
      ((chunks parameters graph width entry rows roots).map List.length).sum := List.length_flatten
  rw [chunks_lengths] at total
  have oracleBound := EnumerationUniformOracle.code_length_bound parameters graph ∅ ∅ width rows roots
    (labels parameters graph width entry).oracle (labels parameters graph width entry).restore matched
  change (EnumerationPrefixOracle.oracleCode parameters graph width rows roots
    (labels parameters graph width entry).oracle (labels parameters graph width entry).restore).length ≤ _ at oracleBound
  have emitBound : emitLength parameters graph width ≤ 3 + 6 * EnumerationCanonicalEmit.Coordinates parameters :=
    EnumerationCanonicalEmit.code_length_bound parameters width 0 (SharedDetectorPrepared.packetSize graph)
  by_cases one : parameters.buses = 1
  all_goals
    simp only [List.sum_cons, List.sum_nil, one, ite_true, ite_false] at total
    omega


end Controller.Cost.EnumerationDriverCode
