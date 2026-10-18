module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.LiteralBits
public import Controller.Cost.SharedTableProbe
public import Controller.Cost.UniformDAGOutputs
public import Mathlib.Algebra.BigOperators.Fin

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Literal sets represented by shared OR propagation. A separate zero flag
retains constant-false ancestors; intersections of the two literal sets detect
contradictions. Singleton probes compute every column of the dense table. -/
namespace Controller.Extensions.LiteralMachine
open Controller.Decoder Controller.Decoder.DAG Controller.Extensions.GateBasis

@[ext] structure Raw (n : Nat) where
  positive : Finset (Channel n)
  negative : Finset (Channel n)
  zero : Bool
  deriving DecidableEq

def Raw.decode (a : Raw n) : Option (GateBasis.Cube n) :=
  if a.zero then none else GateBasis.normalize a.positive a.negative

def Raw.merge (a b : Raw n) : Raw n :=
  ⟨a.positive ∪ b.positive, a.negative ∪ b.negative, a.zero || b.zero⟩

def Raw.guards (a : Raw n) (labels : List (Channel n)) : Raw n :=
  ⟨a.positive, a.negative ∪ labels.toFinset, a.zero⟩

theorem decode_merge (a b : Raw n) :
    (a.merge b).decode = GateBasis.merge a.decode b.decode := by
  by_cases az : a.zero = true
  · simp [Raw.merge, Raw.decode, az, GateBasis.merge]
  by_cases bz : b.zero = true
  · simp [Raw.merge, Raw.decode, bz, GateBasis.merge]
  have af : a.zero = false := by cases h : a.zero <;> simp_all
  have bf : b.zero = false := by cases h : b.zero <;> simp_all
  simp only [Raw.merge, Raw.decode, af, bf, Bool.false_or, Bool.false_eq_true, ite_false]
  by_cases ac : Disjoint a.positive a.negative
  · by_cases bc : Disjoint b.positive b.negative
    · simp [GateBasis.normalize, ac, bc, GateBasis.merge]
    · have combined : ¬ Disjoint (a.positive ∪ b.positive) (a.negative ∪ b.negative) := by
        intro h
        exact bc (Finset.disjoint_left.mpr (fun c hp hn =>
          Finset.disjoint_left.mp h (Finset.mem_union_right _ hp) (Finset.mem_union_right _ hn)))
      simp [GateBasis.normalize, ac, bc, combined, GateBasis.merge]
  · have combined : ¬ Disjoint (a.positive ∪ b.positive) (a.negative ∪ b.negative) := by
      intro h
      exact ac (Finset.disjoint_left.mpr (fun c hp hn =>
        Finset.disjoint_left.mp h (Finset.mem_union_left _ hp) (Finset.mem_union_left _ hn)))
    simp [GateBasis.normalize, ac, combined, GateBasis.merge]

theorem decode_guards (a : Raw n) (labels : List (Channel n)) :
    (a.guards labels).decode = GateBasis.addGuards a.decode labels := by
  by_cases az : a.zero = true
  · simp [Raw.guards, Raw.decode, az, GateBasis.addGuards]
  have af : a.zero = false := by cases h : a.zero <;> simp_all
  simp only [Raw.guards, Raw.decode, af, Bool.false_eq_true, ite_false]
  by_cases ac : Disjoint a.positive a.negative
  · simp [GateBasis.normalize, ac, GateBasis.addGuards]
  · have combined : ¬ Disjoint a.positive (a.negative ∪ labels.toFinset) := by
      rw [Finset.disjoint_union_right]
      tauto
    simp [GateBasis.normalize, ac, combined, GateBasis.addGuards]

def rawGate (gate : Gate n available) (earlier : Fin available → Raw n) : Raw n := match gate with
  | .zero => ⟨∅, ∅, true⟩
  | .input c => ⟨{c}, ∅, false⟩
  | .disj [c] => earlier c
  | .disj _ => ⟨∅, ∅, true⟩
  | .guard c labels => (earlier c).guards labels
  | .liveAnd l r => (earlier l).merge (earlier r)

theorem rawGate_decode (gate : Gate n available) (earlier : Fin available → Raw n) :
    (rawGate gate earlier).decode = GateBasis.literalGate gate (fun child => (earlier child).decode) := by
  cases gate with
  | zero => simp [rawGate, Raw.decode, GateBasis.literalGate]
  | input c => simp [rawGate, Raw.decode, GateBasis.literalGate, GateBasis.normalize]
  | guard c labels => exact decode_guards _ _
  | liveAnd l r => exact decode_merge _ _
  | disj children => cases children with
    | nil => simp [rawGate, Raw.decode, GateBasis.literalGate]
    | cons c rest => cases rest <;> rfl

def summary (graph : DAG n) (root : Fin graph.nodeCount) : Raw n :=
  rawGate (graph.node root) (fun child => summary graph (graph.childIndex root child))
termination_by root.val
decreasing_by exact graph.childIndex_lt root child

theorem summary_decode (graph : DAG n) (root : Fin graph.nodeCount) :
    (summary graph root).decode = GateBasis.literalSummary graph root := by
  have claim : ∀ depth, ∀ i : Fin graph.nodeCount, i.val = depth →
      (summary graph i).decode = GateBasis.literalSummary graph i := by
    intro depth
    induction depth using Nat.strong_induction_on with
    | h depth ih =>
      intro i hi
      rw [summary, rawGate_decode, GateBasis.literalSummary]
      congr 1
      funext child
      exact ih child.val (by have := child.isLt; omega) (graph.childIndex i child) rfl
  exact claim root.val root rfl

/-- Three adjacent values belong to each original node. -/
def nodeId (original : DAG n) (root : Fin original.nodeCount) (lane : Fin 3) :
    Fin (n + 1 + 3 * original.nodeCount) := ⟨n + 1 + 3 * root.val + lane.val, by
  have := root.isLt
  have := lane.isLt
  omega⟩

def liftedGate (gate : Gate n available) (lane : Fin 3) :
    Gate (n + 1) (n + 1 + 3 * available + lane.val) :=
  let child := fun c : Fin available =>
    (⟨n + 1 + 3 * c.val + lane.val, by have := c.isLt; omega⟩ : Fin (n + 1 + 3 * available + lane.val))
  let seed := fun c : Fin (n + 1) =>
    (⟨c.val, by have := c.isLt; omega⟩ : Fin (n + 1 + 3 * available + lane.val))
  match gate with
  | .zero => if lane.val = 2 then .disj [seed ⟨n, by omega⟩] else .zero
  | .input c => if lane.val = 0 then .disj [seed c.castSucc] else .zero
  | .disj [c] => .disj [child c]
  | .disj _ => if lane.val = 2 then .disj [seed ⟨n, by omega⟩] else .zero
  | .guard c labels => .disj (child c :: if lane.val = 1 then labels.map (fun d => seed d.castSucc) else [])
  | .liveAnd l r => .disj [child l, child r]

def graph (original : DAG n) : DAG (n + 1) where
  nodeCount := n + 1 + 3 * original.nodeCount
  node i := if prefixBound : i.val < n + 1 then .input ⟨i.val, prefixBound⟩ else
    let number := (i.val - (n + 1)) / 3
    let lane : Fin 3 := ⟨(i.val - (n + 1)) % 3, Nat.mod_lt _ (by decide)⟩
    let source : Fin original.nodeCount := ⟨number, by have := i.isLt; dsimp [number]; omega⟩
    let gate := liftedGate (original.node source) lane
    have index : n + 1 + 3 * source.val + lane.val = i.val := by dsimp [source, number, lane]; omega
    index ▸ gate
  roots := []

theorem node_seed (original : DAG n) (channel : Fin (n + 1)) :
    (graph original).node ⟨channel.val, by have := channel.isLt; dsimp [graph]; omega⟩ = .input channel := by
  simp [graph, channel.isLt]

theorem node_source (original : DAG n) (root : Fin original.nodeCount) (lane : Fin 3) :
    (graph original).node (nodeId original root lane) = liftedGate (original.node root) lane := by
  have outside : ¬ n + 1 + 3 * root.val + lane.val < n + 1 := by omega
  have quotient : (n + 1 + 3 * root.val + lane.val - (n + 1)) / 3 = root.val := by
    have := lane.isLt
    omega
  have remainder : (n + 1 + 3 * root.val + lane.val - (n + 1)) % 3 = lane.val := by
    have := lane.isLt
    omega
  simp only [graph, nodeId, dite_eq_right outside]
  apply eq_of_heq
  apply (eqRec_heq _ _).trans
  congr 1
  · congr 1
    exact Fin.ext quotient
  · exact Fin.ext remainder

theorem eval_seed (original : DAG n) (values : Assignment (n + 1)) (channel : Fin (n + 1)) :
    (graph original).eval values ⟨channel.val, by have := channel.isLt; dsimp [graph]; omega⟩ = values channel := by
  rw [DAG.eval_eq, node_seed]
  rfl

def bit (labels : Finset (Channel n)) (probe : Fin (n + 1)) : Bool :=
  decide (∃ c : Channel n, c ∈ labels ∧ c.val = probe.val)

@[simp] theorem bit_union (left right : Finset (Channel n)) (probe : Fin (n + 1)) :
    bit (left ∪ right) probe = (bit left probe || bit right probe) := by
  apply Bool.eq_iff_iff.mpr
  simp [bit, or_and_right, exists_or]

@[simp] theorem bit_empty (probe : Fin (n + 1)) : bit (∅ : Finset (Channel n)) probe = false := by
  simp [bit]

@[simp] theorem bit_singleton (c : Channel n) (probe : Fin (n + 1)) :
    bit {c} probe = decide (c.castSucc = probe) := by
  simp only [bit, Finset.mem_singleton, exists_eq_left]
  simp only [Fin.ext_iff, Fin.val_castSucc]

theorem bit_list (labels : List (Channel n)) (probe : Fin (n + 1)) :
    bit labels.toFinset probe = labels.any (fun c => decide (c.castSucc = probe)) := by
  apply Bool.eq_iff_iff.mpr
  simp [bit, List.any_eq_true, Fin.ext_iff]

def flags (a : Raw n) (probe : Fin (n + 1)) (lane : Fin 3) : Bool :=
  if lane.val = 0 then bit a.positive probe
  else if lane.val = 1 then bit a.negative probe
  else a.zero && decide (probe.val = n)

def probeAssignment (probe : Fin (n + 1)) : Assignment (n + 1) := fun c => decide (c = probe)

theorem liftedGate_eval (gate : Gate n available) (lane : Fin 3) (probe : Fin (n + 1))
    (earlier : Fin available → Raw n)
    (values : Fin (n + 1 + 3 * available + lane.val) → Bool)
    (seeds : ∀ c : Fin (n + 1), values ⟨c.val, by have := c.isLt; omega⟩ = decide (c = probe))
    (children : ∀ c : Fin available,
      values ⟨n + 1 + 3 * c.val + lane.val, by have := c.isLt; omega⟩ = flags (earlier c) probe lane) :
    (liftedGate gate lane).eval (probeAssignment probe) values = flags (rawGate gate earlier) probe lane := by
  have lastSeed := seeds ⟨n, by omega⟩
  cases gate with
  | zero => fin_cases lane <;> simp_all [liftedGate, Gate.eval, rawGate, flags, Fin.ext_iff, eq_comm]
  | input c =>
    have seed := seeds c.castSucc
    fin_cases lane <;> simp_all [liftedGate, Gate.eval, rawGate, flags]
  | liveAnd l r =>
    have left := children l
    have right := children r
    fin_cases lane <;> simp_all [liftedGate, Gate.eval, rawGate, flags, Raw.merge, Bool.and_or_distrib_right]
  | guard c labels =>
    have child := children c
    have labelsEq : labels.map (fun d => values ⟨d.val, by have := d.isLt; omega⟩) =
        labels.map (fun d => decide (d.castSucc = probe)) := by
      apply List.map_congr_left
      intro d _
      exact seeds d.castSucc
    have labelsAny := congrArg (fun xs : List Bool => xs.any id) labelsEq
    simp only [List.any_map, Function.comp_def] at labelsAny
    fin_cases lane <;> simp_all [liftedGate, Gate.eval, rawGate, flags, Raw.guards,
      bit_list, List.any_map, Function.comp_def]
  | disj refs =>
    cases refs with
    | nil => fin_cases lane <;> simp_all [liftedGate, Gate.eval, rawGate, flags, Fin.ext_iff, eq_comm]
    | cons c rest =>
      cases rest with
      | nil =>
        have child := children c
        fin_cases lane <;> simp_all [liftedGate, Gate.eval, rawGate, flags]
      | cons d rest => fin_cases lane <;> simp_all [liftedGate, Gate.eval, rawGate, flags, Fin.ext_iff, eq_comm]

theorem eval_flags (original : DAG n) (root : Fin original.nodeCount) (probe : Fin (n + 1)) (lane : Fin 3) :
    (graph original).eval (probeAssignment probe) (nodeId original root lane) = flags (summary original root) probe lane := by
  have claim : ∀ depth, ∀ i : Fin original.nodeCount, i.val = depth → ∀ lane : Fin 3,
      (graph original).eval (probeAssignment probe) (nodeId original i lane) = flags (summary original i) probe lane := by
    intro depth
    induction depth using Nat.strong_induction_on with
    | h depth ih =>
      intro i hi currentLane
      rw [(graph original).eval_eq (probeAssignment probe) (nodeId original i currentLane), node_source, summary]
      apply liftedGate_eval
      · intro c
        change (graph original).eval (probeAssignment probe) ⟨c.val, _⟩ = decide (c = probe)
        exact eval_seed original (probeAssignment probe) c
      · intro c
        change (graph original).eval (probeAssignment probe) (nodeId original (original.childIndex i c) currentLane) = _
        exact ih c.val (by have := c.isLt; omega) (original.childIndex i c) rfl currentLane
  exact claim root.val root rfl lane

theorem node_cases (original : DAG n) (i : Fin (graph original).nodeCount) :
    (∃ c : Fin (n + 1), i.val = c.val) ∨
      ∃ root lane, i = nodeId original root lane := by
  by_cases prefixBound : i.val < n + 1
  · exact Or.inl ⟨⟨i.val, prefixBound⟩, rfl⟩
  · right
    let root : Fin original.nodeCount := ⟨(i.val - (n + 1)) / 3, by have := i.isLt; dsimp [graph] at *; omega⟩
    let lane : Fin 3 := ⟨(i.val - (n + 1)) % 3, Nat.mod_lt _ (by decide)⟩
    refine ⟨root, lane, Fin.ext ?_⟩
    dsimp [nodeId, root, lane]
    omega

theorem lifted_children (gate : Gate n available) (lane : Fin 3) :
    (liftedGate gate lane).children.length ≤ gate.children.length + gate.guardLabels.length + 1 := by
  cases gate with
  | zero => by_cases h : lane.val = 2 <;> simp [liftedGate, h, Gate.children, Gate.guardLabels]
  | input c => by_cases h : lane.val = 0 <;> simp [liftedGate, h, Gate.children, Gate.guardLabels]
  | liveAnd l r => simp [liftedGate, Gate.children, Gate.guardLabels]
  | guard c labels =>
    simp only [liftedGate, Gate.children, Gate.guardLabels, List.length_cons]
    split <;> simp
  | disj refs =>
    cases refs with
    | nil => by_cases h : lane.val = 2 <;> simp [liftedGate, h, Gate.children, Gate.guardLabels]
    | cons c rest =>
      cases rest with
      | nil => simp [liftedGate, Gate.children, Gate.guardLabels]
      | cons d rest => by_cases h : lane.val = 2 <;> simp [liftedGate, h, Gate.children, Gate.guardLabels]

theorem lifted_guards (gate : Gate n available) (lane : Fin 3) :
    (liftedGate gate lane).guardLabels = [] := by
  cases gate with
  | zero => by_cases h : lane.val = 2 <;> simp [liftedGate, h, Gate.guardLabels]
  | input c => by_cases h : lane.val = 0 <;> simp [liftedGate, h, Gate.guardLabels]
  | liveAnd l r => rfl
  | guard c labels => rfl
  | disj refs => cases refs with
    | nil => by_cases h : lane.val = 2 <;> simp [liftedGate, h, Gate.guardLabels]
    | cons c rest =>
      cases rest with
      | nil => rfl
      | cons d rest => by_cases h : lane.val = 2 <;> simp [liftedGate, h, Gate.guardLabels]

theorem guards_empty (original : DAG n) (i : Fin (graph original).nodeCount) :
    ((graph original).node i).guardLabels = [] := by
  rcases node_cases original i with ⟨c, eq⟩ | ⟨root, lane, rfl⟩
  · have eqi : i = ⟨c.val, by have := c.isLt; dsimp [graph]; omega⟩ := Fin.ext eq
    rw [eqi, node_seed]
    rfl
  · rw [node_source]
    exact lifted_guards _ _

theorem source_sum (original : DAG n) (f : Fin (graph original).nodeCount → Nat) :
    (∑ i, f i) =
      (∑ c : Fin (n + 1), f ⟨c.val, by have := c.isLt; dsimp [graph]; omega⟩) +
      ∑ root : Fin original.nodeCount, ∑ lane : Fin 3, f (nodeId original root lane) := by
  change (∑ i : Fin (n + 1 + 3 * original.nodeCount), f i) = _
  let e : Fin original.nodeCount × Fin 3 ≃ Fin (3 * original.nodeCount) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm _ _))
  have suffix : (∑ i : Fin (3 * original.nodeCount), f (Fin.natAdd (n + 1) i)) =
      ∑ root : Fin original.nodeCount, ∑ lane : Fin 3, f (nodeId original root lane) := by
    calc
      _ = ∑ p : Fin original.nodeCount × Fin 3, f (Fin.natAdd (n + 1) (e p)) := (e.sum_comp _).symm
      _ = _ := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro root _
        apply Finset.sum_congr rfl
        intro lane _
        congr 1
        apply Fin.ext
        simp [e, finProdFinEquiv, nodeId, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  calc
    _ = (∑ c : Fin (n + 1), f (Fin.castAdd (3 * original.nodeCount) c)) +
        ∑ i : Fin (3 * original.nodeCount), f (Fin.natAdd (n + 1) i) := Fin.sum_univ_add f
    _ = _ := congrArg (fun x => (∑ c : Fin (n + 1), f (Fin.castAdd (3 * original.nodeCount) c)) + x) suffix

theorem graph_size (original : DAG n) : (graph original).countedSize ≤ 8 * (original.countedSize + 1) := by
  have degrees : (graph original).childIncidences ≤
      3 * (original.childIncidences + original.guardIncidences + original.nodeCount) := by
    simp only [DAG.childIncidences, List.sum_ofFn]
    rw [source_sum]
    simp only [node_seed, Gate.children, List.length_nil, Finset.sum_const_zero, Nat.zero_add, node_source]
    calc
      _ ≤ ∑ root : Fin original.nodeCount, ∑ _lane : Fin 3,
          ((original.node root).children.length + (original.node root).guardLabels.length + 1) := by
        apply Finset.sum_le_sum
        intro root _
        exact Finset.sum_le_sum fun lane _ => lifted_children _ _
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          Finset.sum_add_distrib, Nat.mul_add, Nat.mul_one]
        simp only [← Finset.mul_sum, DAG.guardIncidences, List.sum_ofFn]
        rw [Nat.mul_comm original.nodeCount 3]
        rfl
  have noGuards : (graph original).guardIncidences = 0 := by
    simp only [DAG.guardIncidences, List.sum_ofFn]
    simp [guards_empty]
  have size := original.countedSize_eq
  rw [DAG.countedSize_eq, noGuards]
  change (n + 1) + (n + 1 + 3 * original.nodeCount) + (graph original).childIncidences + 0 + 0 ≤ _
  omega

@[simp] theorem bit_primary (labels : Finset (Channel n)) (c : Channel n) :
    bit labels c.castSucc = decide (c ∈ labels) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bit, decide_eq_true_eq, Fin.val_castSucc]
  constructor
  · rintro ⟨d, member, eq⟩
    exact (Fin.ext eq) ▸ member
  · intro member
    exact ⟨c, member, rfl⟩

def fromColumns (original : DAG n) (root : Fin original.nodeCount) : Raw n where
  positive := LiteralBits.channels (Vector.ofFn fun c : Channel n =>
    (graph original).evalTable (probeAssignment c.castSucc) (nodeId original root 0))
  negative := LiteralBits.channels (Vector.ofFn fun c : Channel n =>
    (graph original).evalTable (probeAssignment c.castSucc) (nodeId original root 1))
  zero := (graph original).evalTable (probeAssignment ⟨n, by omega⟩) (nodeId original root 2)

theorem columns_summary (original : DAG n) (root : Fin original.nodeCount) :
    fromColumns original root = summary original root := by
  apply Raw.ext
  · ext c
    simp [fromColumns, LiteralBits.channels, DAG.evalTable_eq_eval, eval_flags, flags]
  · ext c
    simp [fromColumns, LiteralBits.channels, DAG.evalTable_eq_eval, eval_flags, flags]
  · simp [fromColumns, DAG.evalTable_eq_eval, eval_flags, flags]

theorem columns_correct (original : DAG n) (root : Fin original.nodeCount) :
    (fromColumns original root).decode = GateBasis.literalSummary original root := by
  rw [columns_summary, summary_decode]

def Raw.invalid (a : Raw n) : Bool :=
  a.zero || (List.finRange n).any (fun c => decide (c ∈ a.positive) && decide (c ∈ a.negative))

theorem invalid_iff (a : Raw n) : a.invalid = true ↔ a.decode = none := by
  have collision : ((List.finRange n).any (fun c => decide (c ∈ a.positive) && decide (c ∈ a.negative))) = true ↔
      ¬ Disjoint a.positive a.negative := by
    simp [List.any_eq_true, Finset.disjoint_left]
  cases zero : a.zero with
  | true => simp [Raw.invalid, Raw.decode, zero]
  | false =>
    simp only [Raw.invalid, zero, Bool.false_or, collision, Raw.decode, Bool.false_eq_true, ite_false]
    by_cases disjoint : Disjoint a.positive a.negative <;> simp [GateBasis.normalize, disjoint]

theorem invalid_summary (original : DAG n) (root : Fin original.nodeCount) :
    (summary original root).invalid = true ↔ GateBasis.literalSummary original root = none := by
  rw [invalid_iff, summary_decode]

end Controller.Extensions.LiteralMachine
