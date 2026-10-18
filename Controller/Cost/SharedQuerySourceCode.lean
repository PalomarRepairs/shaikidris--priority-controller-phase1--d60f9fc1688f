module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedQuerySolverCode

public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Controller.Cost.SharedQuerySourceCode
open Controller.Cost.GateProgram Controller.Cost.ForestZeroEmit
open Controller.Cost.ForestZeroAdmissibleCaller

def solverEntry (width entry keep : Nat) (references : List (List (Reference ambient))) : Nat :=
  entry + 15 + (ForestZeroQueryCaller.queryCode width (entry + 15) keep
    (reservedReferences references)).length + 81

@[irreducible] def code (width entry keep : Nat)
    (references : List (List (Reference ambient))) : List (Instruction width 8) :=
  (reuseEntryCode width).toList ++
  (keepCode width).map RegisterWiden.widenInstruction ++
  [.constant 0 (word width (keep + 5 + 2 * (references.length + 1)))] ++
  (constructorCode width (entry + 15) keep keep (keep + 4)
    (solverEntry width entry keep references) references).map RegisterWiden.widenInstruction

theorem code_length : (code width entry keep references).length =
    solverEntry width entry keep references - entry := by
  simp only [code, List.length_append, Array.length_toList, List.length_map,
    reuseEntryCode, List.length_cons, List.length_nil, keepCode_length,
    constructorCode, code_length, solverEntry]
  simp only [List.length_append, ForestZeroAdmissibleCaller.code_length]
  omega

structure Physical (program : Program width 8) (entry keep : Nat)
    (references : List (List (Reference ambient))) : Prop where
  reuse : ∀ phase : Fin 3, program[entry + phase.val]? = (reuseEntryCode width)[phase.val]?
  saved : ForestZeroCallerWiden.WidenedBlockAt program (entry + 3) (keepCode width)
  cursor : program[entry + 14]? = some (.constant 0
    (word width (keep + 5 + 2 * (references.length + 1))))
  constructor : ForestZeroCallerWiden.WidenedBlockAt program (entry + 15)
    (constructorCode width (entry + 15) keep keep (keep + 4)
      (solverEntry width entry keep references) references)

set_option maxRecDepth 4096 in
theorem physical_at (program : Program width 8) (entry keep : Nat)
    (references : List (List (Reference ambient)))
    (present : SharedRootRead.BlockAt program entry (code width entry keep references)) :
    Physical program entry keep references := by
  unfold code at present
  constructor
  · intro phase
    have found := present phase.val (by
      simp only [List.length_append, Array.length_toList, List.length_map,
        reuseEntryCode, List.length_cons, List.length_nil, keepCode_length]
      have := phase.isLt
      omega)
    fin_cases phase
    all_goals simpa [reuseEntryCode, keepCode] using found
  · intro offset bound
    have small : offset < 11 := by simpa using bound
    have found := present (3 + offset) (by
      simp only [List.length_append, Array.length_toList, List.length_map,
        reuseEntryCode, List.length_cons, List.length_nil, keepCode_length]
      omega)
    interval_cases offset
    all_goals simpa [reuseEntryCode, keepCode, RegisterWiden.widenInstruction,
      Nat.add_assoc] using found
  · have found := present 14 (by
      simp only [List.length_append, Array.length_toList, List.length_map,
        reuseEntryCode, List.length_cons, List.length_nil, keepCode_length]
      omega)
    simpa [reuseEntryCode, keepCode] using found
  · intro offset bound
    have prefixLength : ((reuseEntryCode width).toList ++
        (keepCode width).map RegisterWiden.widenInstruction ++
        [(Instruction.constant 0 (word width (keep + 5 + 2 * (references.length + 1))) : Instruction width 8)]).length = 15 := by
      simp [reuseEntryCode]
    have prepared : SharedRootRead.BlockAt program entry
        (((reuseEntryCode width).toList ++ (keepCode width).map RegisterWiden.widenInstruction ++
          [.constant 0 (word width (keep + 5 + 2 * (references.length + 1)))]) ++
          (constructorCode width (entry + 15) keep keep (keep + 4)
            (solverEntry width entry keep references) references).map RegisterWiden.widenInstruction ++ []) := by
      simpa only [List.append_assoc, List.append_nil] using present
    have block := SharedNativeSuccessCode.segment program entry _ _ _ prepared
    rw [prefixLength] at block
    simpa only [List.getElem?_map] using block offset (by simpa using bound)

theorem root_entry_irrel (graph : Controller.Decoder.DAG n) (b : Nat) (target : Fin n)
    (T F : Finset (Fin n)) (base slot entry keep : Nat) (left right : Fin graph.nodeCount) :
    solverEntry width entry keep (SharedZeroSource.references graph b target T F base slot left) =
    solverEntry width entry keep (SharedZeroSource.references graph b target T F base slot right) := by
  have same := congrArg List.length (SharedZeroSource.constructor_shared (width := width)
    (entry := entry + 15) (protectedEnd := keep) (recordHeader := keep)
    (endHeader := keep + 4) (returnPC := 0) graph b target T F left right
    (base := base) (slot := slot))
  simp only [constructorCode, List.length_append, ForestZeroAdmissibleCaller.code_length] at same
  unfold solverEntry
  omega

theorem root_code_irrel (graph : Controller.Decoder.DAG n) (b : Nat) (target : Fin n)
    (T F : Finset (Fin n)) (base slot entry keep : Nat) (left right : Fin graph.nodeCount) :
    code width entry keep (SharedZeroSource.references graph b target T F base slot left) =
    code width entry keep (SharedZeroSource.references graph b target T F base slot right) := by
  have sameEntry := root_entry_irrel (width := width) graph b target T F base slot entry keep left right
  have sameRows := SharedZeroSource.references_length_root_irrel (base := base) (slot := slot) graph b target T F left right
  unfold code
  rw [sameEntry, sameRows]
  rw [SharedZeroSource.constructor_shared graph b target T F left right]

end Controller.Cost.SharedQuerySourceCode
