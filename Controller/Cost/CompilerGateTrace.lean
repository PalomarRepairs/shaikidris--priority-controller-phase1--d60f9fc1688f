module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.CompilerCellsTrace

@[expose] public section

/-! Composition of actual incidence mapping, cell layout and outer append
traversals for every gate-code branch. Fixed templates and word arithmetic
are not asserted to be fetched RAM compiler operations. -/
namespace Controller.Cost.CompilerGateTrace
open Controller.Decoder Controller.Cost.GateProgram
open Controller.Cost.CompilerAppendTrace Controller.Cost.CompilerCellsTrace

def WrapTrace (front body suffix result : List α) (visits : Nat) : Prop :=
  ∃ middle first second, AppendTrace front body middle first ∧
    AppendTrace middle suffix result second ∧ visits = first + second

theorem wrap_exists (front body suffix : List α) :
    WrapTrace front body suffix ((front ++ body) ++ suffix)
      (2 * front.length + body.length) := by
  exact ⟨front ++ body, front.length, (front ++ body).length,
    append_exists front body, append_exists (front ++ body) suffix, by simp; omega⟩

theorem wrap_exact (trace : WrapTrace front body suffix result visits) :
    result = (front ++ body) ++ suffix ∧ visits = 2 * front.length + body.length := by
  obtain ⟨middle, first, second, left, right, cost⟩ := trace
  obtain ⟨middleEq, firstEq⟩ := append_exact left
  obtain ⟨resultEq, secondEq⟩ := append_exact right
  exact ⟨by simpa [middleEq] using resultEq, by simp [cost, firstEq, secondEq, middleEq]; omega⟩

def GateTrace (width base : Nat) (gate : Gate n available) (result : Code width) (visits : Nat) : Prop :=
  match gate with
  | .zero => result = gateCode width base gate ∧ visits = 0
  | .input _ => result = gateCode width base gate ∧ visits = 0
  | .disj children =>
    ∃ addresses body mapped laid wrapped,
      MapTrace (fun child => n + child.val) children addresses mapped ∧
      CellsTrace (orCell width) 4 (base + 1) addresses body laid ∧
      WrapTrace [.constant 2 (boolWord width false)] body [.allocate 2] result wrapped ∧
      visits = mapped + laid + wrapped
  | .guard child labels =>
    ∃ addresses body mapped laid wrapped,
      MapTrace Fin.val labels addresses mapped ∧
      CellsTrace (guardCell width) 4 (base + 2) addresses body laid ∧
      WrapTrace [.constant 0 (word width (n + child.val)), .load 2 0] body [.allocate 2] result wrapped ∧
      visits = mapped + laid + wrapped
  | .liveAnd left right =>
    ∃ body laid wrapped,
      CellsTrace (andCell width) 5 (base + 1) [n + left.val, n + right.val] body laid ∧
      WrapTrace [.constant 2 (boolWord width true)] body [.allocate 2] result wrapped ∧
      visits = laid + wrapped

def traversalCost : Gate n available → Nat
  | .zero => 0
  | .input _ => 0
  | .disj children => 10 * children.length + 2
  | .guard _ labels => 10 * labels.length + 4
  | .liveAnd _ _ => 24

theorem gate_exists (width base : Nat) (gate : Gate n available) :
    GateTrace width base gate (gateCode width base gate) (traversalCost gate) := by
  cases gate with
  | zero => exact ⟨rfl, rfl⟩
  | input channel => exact ⟨rfl, rfl⟩
  | disj children =>
    let addresses := children.map (fun child => n + child.val)
    let body := cells (orCell width) 4 (base + 1) addresses
    refine ⟨addresses, body, children.length, 5 * addresses.length, 2 + body.length,
      map_exists _ _, or_cells _ _ _, ?_, ?_⟩
    · simpa only [gateCode, List.length_cons, List.length_nil, Nat.mul_one] using
        wrap_exists ([.constant 2 (boolWord width false)] : Code width) body [.allocate 2]
    · simp [traversalCost, body, addresses, cells_length (orCell width) 4 (by intros; rfl)]; omega
  | guard child labels =>
    let addresses := labels.map Fin.val
    let body := cells (guardCell width) 4 (base + 2) addresses
    refine ⟨addresses, body, labels.length, 5 * addresses.length, 4 + body.length,
      map_exists _ _, guard_cells _ _ _, ?_, ?_⟩
    · simpa only [gateCode, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] using
        wrap_exists ([.constant 0 (word width (n + child.val)), .load 2 0] : Code width) body [.allocate 2]
    · simp [traversalCost, body, addresses, cells_length (guardCell width) 4 (by intros; rfl)]; omega
  | liveAnd left right =>
    let body := cells (andCell width) 5 (base + 1) [n + left.val, n + right.val]
    refine ⟨body, 12, 2 + body.length, and_cells _ _ _, ?_, ?_⟩
    · simpa only [gateCode, List.length_cons, List.length_nil, Nat.mul_one] using
        wrap_exists ([.constant 2 (boolWord width true)] : Code width) body [.allocate 2]
    · rfl

theorem traversalCost_le (gate : Gate n available) :
    traversalCost gate ≤ 24 * (1 + gate.children.length + gate.guardLabels.length) := by
  cases gate <;> simp [traversalCost, Gate.children, Gate.guardLabels] <;> omega

end Controller.Cost.CompilerGateTrace
