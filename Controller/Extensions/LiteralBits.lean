module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.BasisShared

@[expose] public section

/-! Literal summaries stored as channel bit vectors. Each topological node
owns one positive vector, one negative vector, and a contradiction flag. -/
namespace Controller.Extensions.LiteralBits
open Controller.Decoder Controller.Decoder.DAG Controller.Extensions.GateBasis

variable {n : ℕ}

structure Cube (n : ℕ) where
  positive : Vector Bool n
  negative : Vector Bool n
  deriving DecidableEq, Repr

def channels (bits : Vector Bool n) : Finset (Channel n) :=
  Finset.univ.filter fun c => bits[c.val] = true

@[simp] theorem mem_channels (bits : Vector Bool n) (c : Channel n) :
    c ∈ channels bits ↔ bits[c.val] = true := by simp [channels]

def decode (c : Cube n) : GateBasis.Cube n := ⟨channels c.positive,channels c.negative⟩

def empty : Vector Bool n := Vector.replicate n false

def singleton (c : Channel n) : Vector Bool n := (empty (n := n)).set c.val true

@[simp] theorem channels_empty : channels (empty (n := n)) = ∅ := by ext c; simp [empty]

@[simp] theorem channels_singleton (c : Channel n) : channels (singleton c) = {c} := by
  ext u
  simp [channels,singleton,empty,Vector.getElem_set,Fin.ext_iff,eq_comm]

def union (a b : Vector Bool n) : Vector Bool n := a.zipWith (· || ·) b

@[simp] theorem channels_union (a b : Vector Bool n) : channels (union a b) = channels a ∪ channels b := by
  ext c
  simp [union]

/-- One dense scan detects conflicting signs. -/
def consistent (c : Cube n) : Bool :=
  (List.finRange n).all fun i => !(c.positive[i.val] && c.negative[i.val])

theorem consistent_iff (c : Cube n) : consistent c = true ↔ Disjoint (channels c.positive) (channels c.negative) := by
  simp only [consistent,List.all_eq_true]
  rw [Finset.disjoint_left]
  constructor
  · intro h i hp hn
    have value := h i (List.mem_finRange i)
    rw [(mem_channels _ _).mp hp,(mem_channels _ _).mp hn] at value
    contradiction
  · intro h i _
    have no : ¬ (c.positive[i.val] = true ∧ c.negative[i.val] = true) := by
      rintro ⟨hp,hn⟩
      exact h ((mem_channels _ _).mpr hp) ((mem_channels _ _).mpr hn)
    cases hp : c.positive[i.val] <;> cases hn : c.negative[i.val] <;> simp_all

def normalize (c : Cube n) : Option (Cube n) := if consistent c then some c else none

theorem decode_normalize (c : Cube n) :
    (normalize c).map decode = GateBasis.normalize (channels c.positive) (channels c.negative) := by
  by_cases yes : consistent c = true
  · simp [normalize,yes,GateBasis.normalize,(consistent_iff c).mp yes,decode]
  · have no := (consistent_iff c).not.mp yes
    simp [normalize,yes,GateBasis.normalize,no]

def merge (a b : Option (Cube n)) : Option (Cube n) := do
  let a ← a
  let b ← b
  normalize ⟨union a.positive b.positive,union a.negative b.negative⟩

theorem decode_merge (a b : Option (Cube n)) :
    (merge a b).map decode = GateBasis.merge (a.map decode) (b.map decode) := by
  cases a <;> cases b <;> simp [merge,GateBasis.merge,decode_normalize,channels_union,decode]

/-- Copying a child's vector is charged once per node; repeated guards are
individual indexed writes to that node's negative vector. -/
def mark (bits : Vector Bool n) (labels : List (Channel n)) : Vector Bool n :=
  labels.foldl (fun mask c => mask.set c.val true) bits

theorem channels_mark (bits : Vector Bool n) (labels : List (Channel n)) :
    channels (mark bits labels) = channels bits ∪ labels.toFinset := by
  induction labels generalizing bits with
  | nil => simp [mark]
  | cons c rest ih =>
    simp only [mark,List.foldl_cons] at *
    rw [ih]
    have set : channels (bits.set c.val true) = insert c (channels bits) := by
      ext u
      by_cases eq : c = u
      · subst u; simp
      · have vals : c.val ≠ u.val := fun h => eq (Fin.ext h)
        simp [Vector.getElem_set_ne c.isLt u.isLt vals,Ne.symm eq]
    rw [set]
    ext u
    simp [or_comm]

def addGuards (a : Option (Cube n)) (labels : List (Channel n)) : Option (Cube n) := do
  let a ← a
  normalize ⟨a.positive,mark a.negative labels⟩

theorem decode_addGuards (a : Option (Cube n)) (labels : List (Channel n)) :
    (addGuards a labels).map decode = GateBasis.addGuards (a.map decode) labels := by
  cases a <;> simp [addGuards,GateBasis.addGuards,decode_normalize,channels_mark,decode]

def literalGate (gate : Gate n available) (earlier : Fin available → Option (Cube n)) :
    Option (Cube n) := match gate with
  | .zero => none
  | .input c => some ⟨singleton c,empty⟩
  | .disj [c] => earlier c
  | .disj _ => none
  | .guard c labels => addGuards (earlier c) labels
  | .liveAnd l r => merge (earlier l) (earlier r)

theorem decode_literalGate (gate : Gate n available) (earlier : Fin available → Option (Cube n)) :
    (literalGate gate earlier).map decode = GateBasis.literalGate gate (fun c => (earlier c).map decode) := by
  cases gate with
  | zero => rfl
  | input c => simp [literalGate,GateBasis.literalGate,decode]
  | guard c labels => exact decode_addGuards _ _
  | liveAnd l r => exact decode_merge _ _
  | disj refs => cases refs with
    | nil => rfl
    | cons c rest => cases rest <;> rfl

/-- A vector push executes each represented node once and preserves sharing. -/
def buildPrefix (graph : DAG n) : (length : ℕ) → length ≤ graph.nodeCount → Vector (Option (Cube n)) length
  | 0,_ => #v[]
  | length+1,bound =>
    let earlier := buildPrefix graph length (Nat.le_trans (Nat.le_succ _) bound)
    let gate := graph.node ⟨length,by omega⟩
    earlier.push (literalGate gate (fun child => earlier[child.val]))

theorem prefix_correct (graph : DAG n) : ∀ length bound (i : Fin length),
    ((buildPrefix graph length bound)[i.val]).map decode = GateBasis.summaryPrefix graph length bound i := by
  intro length
  induction length with
  | zero => intro bound i; exact Fin.elim0 i
  | succ length ih =>
    intro bound i
    refine Fin.lastCases ?_ (fun c => ?_) i
    · simp only [buildPrefix,Fin.val_last,Vector.getElem_push_eq,GateBasis.summaryPrefix,Fin.lastCases_last]
      rw [decode_literalGate]
      congr 1
      funext c
      exact ih _ c
    · simp only [buildPrefix,Fin.val_castSucc,Vector.getElem_push_lt c.isLt,GateBasis.summaryPrefix,Fin.lastCases_castSucc]
      exact ih _ c

def table (graph : DAG n) : Vector (Option (Cube n)) graph.nodeCount := buildPrefix graph graph.nodeCount le_rfl

theorem table_correct (graph : DAG n) (i : Fin graph.nodeCount) :
    ((table graph)[i.val]).map decode = summaryTable graph i := prefix_correct graph _ _ i

/-- Exact resident payload for the dense summaries, including one validity
flag per stored node; source and query scratch are accounted separately. -/
def tableWords (graph : DAG n) : ℕ := graph.nodeCount*(2*n+1)

theorem tableWords_bound (graph : DAG n) : tableWords graph ≤ (2*n+1)*graph.countedSize := by
  have size := graph.countedSize_eq
  unfold tableWords
  rw [Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (by omega)

/-- Read the actual bit-vector table once and share it across observations. -/
def literalSearch (graph : DAG n) (b : ℕ) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) : Option (Finset (Channel n)) :=
  let summaries := table graph
  firstSuccess (fun root => cubeSearch b target ((summaries[root.val]).map decode) (!healthy root)) graph.roots

theorem literalSearch_eq (graph : DAG n) (b : ℕ) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) :
    literalSearch graph b target healthy = BasisShared.literalSearch graph b target healthy := by
  unfold literalSearch BasisShared.literalSearch
  dsimp only
  congr 1
  funext root
  rw [table_correct]
  rfl

theorem literalSearch_some (graph : DAG n) (noOr : NoDisjunction graph)
    (b : ℕ) (target : Channel n) (healthy : Fin graph.nodeCount → Bool) (K : Finset (Channel n))
    (returned : literalSearch graph b target healthy = some K) :
    Admissible b target K ∧ ∃ root ∈ graph.roots, graph.eval (assignmentOfSet K) root ≠ healthy root := by
  rw [literalSearch_eq] at returned
  exact BasisShared.literalSearch_some graph noOr b target healthy K returned

theorem literalSearch_none_iff (graph : DAG n) (noOr : NoDisjunction graph)
    (b : ℕ) (target : Channel n) (healthy : Fin graph.nodeCount → Bool) :
    literalSearch graph b target healthy = none ↔
      ¬ ∃ root ∈ graph.roots, ∃ K, Admissible b target K ∧ graph.eval (assignmentOfSet K) root ≠ healthy root := by
  rw [literalSearch_eq]
  exact BasisShared.literalSearch_none_iff graph noOr b target healthy

/-- Proper-basis dispatch with the concrete dense no-OR table. -/
def detectSet (graph : DAG n) (B : Basis) (b : ℕ) (target : Channel n) (drive : Bool) :
    Option (Finset (Channel n)) :=
  if drive then
    if B.conjunction = false then GateBasis.detectSet graph B b target drive
    else
      let healthy := graph.evalTable (assignmentOfSet {target})
      if B.negativeGuard = false then BasisShared.monotoneSearch graph b target healthy
      else literalSearch graph b target healthy
  else none

theorem detectSet_eq (graph : DAG n) (B : Basis) (b : ℕ) (target : Channel n) (drive : Bool) :
    detectSet graph B b target drive = BasisShared.detectSet graph B b target drive := by
  simp only [detectSet,BasisShared.detectSet,literalSearch_eq]

theorem detectSet_some (graph : DAG n) (B : Basis) (uses : Uses graph B) (proper : B ≠ full)
    (b : ℕ) (target : Channel n) (drive : Bool) (K : Finset (Channel n))
    (returned : detectSet graph B b target drive = some K) :
    drive = true ∧ Admissible b target K ∧ ∃ root ∈ graph.roots,
      graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root := by
  rw [detectSet_eq] at returned
  exact BasisShared.detectSet_some graph B uses proper b target drive K returned

theorem detectSet_none_iff (graph : DAG n) (B : Basis) (uses : Uses graph B) (proper : B ≠ full)
    (b : ℕ) (target : Channel n) (drive : Bool) :
    detectSet graph B b target drive = none ↔
      ¬ (drive = true ∧ ∃ root ∈ graph.roots, ∃ K, Admissible b target K ∧
        graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root) := by
  rw [detectSet_eq]
  exact BasisShared.detectSet_none_iff graph B uses proper b target drive

end Controller.Extensions.LiteralBits
