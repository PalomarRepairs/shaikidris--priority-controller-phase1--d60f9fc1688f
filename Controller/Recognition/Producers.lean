module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.CNF.Tseitin
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-! Complete producer certificates and order-independent recovery.

The descendant premise in producer recovery is directed reachability in the
intended DAG. It is stronger than being later in a topological numbering.
Candidate discovery and its completeness are not part of these certificates.
-/

namespace Controller.Recognition
open Controller.CNF

structure Producer (α : Type*) where
  output : Literal α
  gate : Gate α
  deriving DecidableEq

namespace Producer

def Ready [DecidableEq α] (known : Finset α) (p : Producer α) : Prop :=
  p.output.1 ∉ known ∧ ∀ l ∈ p.gate.inputs, l.1 ∈ known

def Complete [DecidableEq α] (p : Producer α) (block : Formula α) : Prop :=
  Gate.CompleteProducer block p.output p.gate

instance [DecidableEq α] (known : Finset α) (p : Producer α) :
    Decidable (p.Ready known) := inferInstanceAs (Decidable (_ ∧ ∀ _, ∀ _, _))

instance [DecidableEq α] (p : Producer α) (block : Formula α) :
    Decidable (p.Complete block) :=
  inferInstanceAs (Decidable (Gate.CompleteProducer block p.output p.gate))

theorem complete_correct [DecidableEq α] (p : Producer α) (block : Formula α)
    (h : p.Complete block) (a : α → Bool) :
    Satisfies a block ↔ literalValue a p.output = p.gate.eval a :=
  Gate.CompleteProducer.correct h a

end Producer

/-- The record retains every selected original row occurrence by its source ID.
The complete-block test checks both implication directions on this local list. -/
structure BlockRecord (α : Type*) (source : Formula α) where
  producer : Producer α
  origins : List (Fin source.clauses.size)

namespace BlockRecord

def localFormula (b : BlockRecord α source) : Formula α :=
  ofClauses (b.origins.map (fun i => source.clauses[i]))

def Valid [DecidableEq α] (b : BlockRecord α source) : Prop :=
  b.producer.Complete b.localFormula

instance [DecidableEq α] (b : BlockRecord α source) : Decidable b.Valid :=
  inferInstanceAs (Decidable (b.producer.Complete b.localFormula))

theorem source_implies [DecidableEq α] (b : BlockRecord α source)
    (valid : b.Valid) (a : α → Bool) (model : Satisfies a source) :
    literalValue a b.producer.output = b.producer.gate.eval a := by
  apply (b.producer.complete_correct b.localFormula valid a).mp
  rw [localFormula, satisfies_ofClauses]
  intro row member
  obtain ⟨origin, _, rfl⟩ := List.mem_map.mp member
  exact (satisfies_iff_rows a source).mp model origin

end BlockRecord

/-- Root producers have no inputs. Every dependency has strictly smaller rank. -/
structure IntendedDAG (α : Type*) [DecidableEq α] where
  roots : Finset α
  gate : α → Gate α
  phase : α → Bool
  rank : α → Nat
  roots_empty : ∀ v ∈ roots, (gate v).inputs = []
  earlier : ∀ v l, l ∈ (gate v).inputs → rank l.1 < rank v

namespace IntendedDAG
variable [DecidableEq α]

def producer (dag : IntendedDAG α) (v : α) : Producer α :=
  ⟨(v, dag.phase v), dag.gate v⟩

/-- The second argument is a proper descendant of the first argument. -/
inductive Descendant (dag : IntendedDAG α) : α → α → Prop where
  | edge {x y : α} (l : Literal α) (member : l ∈ (dag.gate y).inputs)
      (source : l.1 = x) : Descendant dag x y
  | trans {x y z : α} : Descendant dag x y → Descendant dag y z → Descendant dag x z

theorem Descendant.rank_lt (dag : IntendedDAG α) {x y : α}
    (h : dag.Descendant x y) : dag.rank x < dag.rank y := by
  induction h with
  | edge l member source => simpa only [source] using dag.earlier _ l member
  | trans _ _ first second => exact Nat.lt_trans first second

theorem no_descendant_cycle (dag : IntendedDAG α) (v : α) :
    ¬dag.Descendant v v := fun h => Nat.lt_irrefl _ (Descendant.rank_lt dag h)

def Closed (dag : IntendedDAG α) (known : Finset α) : Prop :=
  ∀ v ∈ known, ∀ l ∈ (dag.gate v).inputs, l.1 ∈ known

theorem roots_closed (dag : IntendedDAG α) : dag.Closed dag.roots := by
  intro v member l input
  rw [dag.roots_empty v member] at input
  exact False.elim (List.not_mem_nil input)

theorem Closed.ancestor (dag : IntendedDAG α) {known : Finset α}
    (h : dag.Closed known) {x y : α} (path : dag.Descendant x y)
    (hy : y ∈ known) : x ∈ known := by
  induction path with
  | edge l member source => simpa only [source] using h _ hy l member
  | trans _ _ first second => exact first (second hy)

/-- A candidate for an unknown signal is either its intended producer or
mentions a proper descendant among its input literals. -/
structure CandidatePromise (dag : IntendedDAG α) where
  candidates : List (Producer α)
  coverage : ∀ v, v ∉ dag.roots → dag.producer v ∈ candidates
  no_root : ∀ p ∈ candidates, p.output.1 ∉ dag.roots
  alternatives : ∀ p ∈ candidates, p = dag.producer p.output.1 ∨
    ∃ l ∈ p.gate.inputs, dag.Descendant p.output.1 l.1

theorem ready_is_intended (dag : IntendedDAG α) (promise : dag.CandidatePromise)
    {known : Finset α} (closed : dag.Closed known) {p : Producer α}
    (member : p ∈ promise.candidates) (ready : p.Ready known) :
    p = dag.producer p.output.1 := by
  rcases promise.alternatives p member with intended | ⟨l, input, descendant⟩
  · exact intended
  · exact False.elim (ready.1 (Closed.ancestor dag closed descendant (ready.2 l input)))

theorem insert_closed (dag : IntendedDAG α) {known : Finset α}
    (closed : dag.Closed known) {p : Producer α} (ready : p.Ready known)
    (intended : p = dag.producer p.output.1) : dag.Closed (insert p.output.1 known) := by
  intro v member l input
  rcases Finset.mem_insert.mp member with same | old
  · subst v
    have gates : p.gate = dag.gate p.output.1 := congrArg Producer.gate intended
    exact Finset.mem_insert_of_mem (ready.2 l (gates.symm ▸ input))
  · exact Finset.mem_insert_of_mem (closed v old l input)

/-- Each step may choose any currently ready candidate. No iteration order is fixed. -/
inductive Run (dag : IntendedDAG α) (promise : dag.CandidatePromise) :
    Finset α → List (Producer α) → Prop where
  | start : Run dag promise dag.roots []
  | step {known trace} (previous : Run dag promise known trace) (p : Producer α)
      (member : p ∈ promise.candidates) (ready : p.Ready known) :
      Run dag promise (insert p.output.1 known) (p :: trace)

theorem Run.closed (dag : IntendedDAG α) (promise : dag.CandidatePromise)
    {known trace} (run : dag.Run promise known trace) : dag.Closed known := by
  induction run with
  | start => exact dag.roots_closed
  | step _ p member ready previous =>
    exact dag.insert_closed previous ready (dag.ready_is_intended promise previous member ready)

theorem Run.intended (dag : IntendedDAG α) (promise : dag.CandidatePromise)
    {known trace} (run : dag.Run promise known trace) :
    ∀ p ∈ trace, p = dag.producer p.output.1 := by
  induction run with
  | start => simp
  | step previous p member ready ih =>
    intro q selected
    rcases List.mem_cons.mp selected with rfl | earlier
    · exact dag.ready_is_intended promise (Run.closed dag promise previous) member ready
    · exact ih q earlier

theorem Run.roots_known (dag : IntendedDAG α) (promise : dag.CandidatePromise)
    {known trace} (run : dag.Run promise known trace) : dag.roots ⊆ known := by
  induction run with
  | start => exact fun _ h => h
  | step _ _ _ _ ih => exact fun _ h => Finset.mem_insert_of_mem (ih h)

/-- Freshness gives strict progress at each selected producer. -/
theorem Run.size_eq (dag : IntendedDAG α) (promise : dag.CandidatePromise)
    {known trace} (run : dag.Run promise known trace) :
    known.card = dag.roots.card + trace.length := by
  induction run with
  | start => simp
  | step _ p _ ready ih =>
    rw [Finset.card_insert_of_notMem ready.1, ih]
    simp only [List.length_cons, Nat.add_assoc]

/-- No choice sequence can exceed the finite signal universe. -/
theorem Run.length_bound [Fintype α] (dag : IntendedDAG α) (promise : dag.CandidatePromise)
    {known trace} (run : dag.Run promise known trace) : trace.length ≤ Fintype.card α := by
  have lower : trace.length ≤ known.card := by
    rw [Run.size_eq dag promise run]
    exact Nat.le_add_left _ _
  exact lower.trans (Finset.card_le_univ known)

/-- If no ready candidate remains, every intended signal has been recovered. -/
theorem saturated_complete (dag : IntendedDAG α) (promise : dag.CandidatePromise)
    {known trace} (run : dag.Run promise known trace)
    (saturated : ∀ p ∈ promise.candidates, ¬p.Ready known) : ∀ v, v ∈ known := by
  have byRank : ∀ k, ∀ v, dag.rank v = k → v ∈ known := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v rankEq
      by_cases member : v ∈ known
      · exact member
      · have notRoot : v ∉ dag.roots := fun h => member ((Run.roots_known dag promise run) h)
        have ready : (dag.producer v).Ready known := by
          refine ⟨member, ?_⟩
          intro l input
          exact ih (dag.rank l.1) (rankEq ▸ dag.earlier v l input) l.1 rfl
        exact False.elim (saturated _ (promise.coverage v notRoot) ready)
  intro v
  exact byRank (dag.rank v) v rfl

/-- Every requested sink lies in the completed known set, regardless of choices. -/
theorem recovered_sinks (dag : IntendedDAG α) (promise : dag.CandidatePromise)
    {known trace} (run : dag.Run promise known trace)
    (saturated : ∀ p ∈ promise.candidates, ¬p.Ready known) (sinks : List α) :
    ∀ v ∈ sinks, v ∈ known := fun v _ => dag.saturated_complete promise run saturated v

end IntendedDAG

/-- Check output ownership, exhaustive producer coverage, no duplicates, and
strict dependency ranks. A rank is a certificate, not inferred from positions. -/
def ValidSelection [DecidableEq α] (roots : Finset α) (rank : α → Nat)
    (selected : List (Producer α)) : Prop :=
  (selected.map (fun p => p.output.1)).Nodup ∧
  (∀ p ∈ selected, p.output.1 ∉ roots) ∧
  (∀ v, v ∉ roots → ∃ p ∈ selected, p.output.1 = v) ∧
  (∀ p ∈ selected, ∀ l ∈ p.gate.inputs, rank l.1 < rank p.output.1)

theorem validSelection_no_self_input [DecidableEq α] {roots : Finset α}
    {rank : α → Nat} {selected : List (Producer α)}
    (valid : ValidSelection roots rank selected) {p : Producer α} (member : p ∈ selected)
    {l : Literal α} (input : l ∈ p.gate.inputs) : l.1 ≠ p.output.1 := by
  intro same
  have smaller := valid.2.2.2 p member l input
  rw [same] at smaller
  exact Nat.lt_irrefl _ smaller

instance [DecidableEq α] [Fintype α] (roots : Finset α) (rank : α → Nat)
    (selected : List (Producer α)) : Decidable (ValidSelection roots rank selected) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

inductive SelectionPath (selected : List (Producer α)) : α → α → Prop where
  | edge (p) (member : p ∈ selected) (l) (input : l ∈ p.gate.inputs) :
      SelectionPath selected l.1 p.output.1
  | trans {x y z} : SelectionPath selected x y → SelectionPath selected y z →
      SelectionPath selected x z

theorem SelectionPath.rank_lt [DecidableEq α] {roots : Finset α} {rank : α → Nat}
    {selected : List (Producer α)} (valid : ValidSelection roots rank selected)
    {x y : α} (path : SelectionPath selected x y) : rank x < rank y := by
  induction path with
  | edge p member l input => exact valid.2.2.2 p member l input
  | trans _ _ first second => exact Nat.lt_trans first second

theorem validSelection_no_cycle [DecidableEq α] {roots : Finset α} {rank : α → Nat}
    {selected : List (Producer α)} (valid : ValidSelection roots rank selected) (v : α) :
    ¬SelectionPath selected v v := fun path => Nat.lt_irrefl _ (SelectionPath.rank_lt valid path)

private theorem all_values_congr (a b : α → Bool) (ls : List (Literal α))
    (same : ∀ l ∈ ls, literalValue a l = literalValue b l) :
    ls.all (literalValue a) = ls.all (literalValue b) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.all_cons, same l (List.mem_cons_self ..),
      ih (fun k hk => same k (List.mem_cons_of_mem _ hk))]

private theorem any_values_congr (a b : α → Bool) (ls : List (Literal α))
    (same : ∀ l ∈ ls, literalValue a l = literalValue b l) :
    ls.any (literalValue a) = ls.any (literalValue b) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.any_cons, same l (List.mem_cons_self ..),
      ih (fun k hk => same k (List.mem_cons_of_mem _ hk))]

theorem gate_eval_inputs_congr (a b : α → Bool) (gate : Gate α)
    (same : ∀ l ∈ gate.inputs, a l.1 = b l.1) : gate.eval a = gate.eval b := by
  have literals : ∀ l ∈ gate.inputs, literalValue a l = literalValue b l := by
    intro l member
    simp only [literalValue, same l member]
  cases gate with
  | and ls => exact all_values_congr a b ls literals
  | or ls => exact any_values_congr a b ls literals
  | xor l r => simp only [Gate.eval, literals l (by simp [Gate.inputs]),
      literals r (by simp [Gate.inputs])]
  | «alias» l => exact literals l (by simp [Gate.inputs])
  | not l => simp only [Gate.eval, literals l (by simp [Gate.inputs])]
  | constant value => rfl

/-- Selected complete equations plus root values determine all recovered signals.
Coverage and actual dependency ranks are used, not candidate-search success. -/
theorem validSelection_unique [DecidableEq α] {roots : Finset α} {rank : α → Nat}
    {selected : List (Producer α)} (valid : ValidSelection roots rank selected)
    (a b : α → Bool) (rootEq : ∀ v ∈ roots, a v = b v)
    (equationsA : ∀ p ∈ selected, literalValue a p.output = p.gate.eval a)
    (equationsB : ∀ p ∈ selected, literalValue b p.output = p.gate.eval b) : a = b := by
  have byRank : ∀ k, ∀ v, rank v = k → a v = b v := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v rankEq
      by_cases root : v ∈ roots
      · exact rootEq v root
      · obtain ⟨p, member, outputEq⟩ := valid.2.2.1 v root
        have dependencies : ∀ l ∈ p.gate.inputs, a l.1 = b l.1 := by
          intro l input
          have lower := valid.2.2.2 p member l input
          rw [outputEq, rankEq] at lower
          exact ih (rank l.1) lower l.1 rfl
        have equal : literalValue a p.output = literalValue b p.output :=
          (equationsA p member).trans
            ((gate_eval_inputs_congr a b p.gate dependencies).trans (equationsB p member).symm)
        have idEq : a p.output.1 = b p.output.1 := by
          cases ha : a p.output.1 <;> cases hb : b p.output.1 <;>
            cases hp : p.output.2 <;> simp_all [literalValue]
        simpa only [outputEq] using idEq
  funext v
  exact byRank (rank v) v rfl

/-- The finite allocation certificate exposes roots first and defines each fresh
output only from earlier variables. Root roles and signal phases are explicit. -/
structure CheckedSelection (α : Type*) where
  rootCount : Nat
  variableCount : Nat
  circuit : AcyclicCircuit rootCount variableCount
  identity : Fin variableCount ≃ α
  phase : Fin variableCount → Bool

namespace CheckedSelection

def formula (s : CheckedSelection α) : Formula α :=
  signedRelabel s.identity s.phase s.circuit.formula

def rootValues (s : CheckedSelection α) (a : α → Bool) : Fin s.rootCount → Bool :=
  s.circuit.rootValues (signedPullback s.identity s.phase a)

theorem existsUnique_extension (s : CheckedSelection α) (roots : Fin s.rootCount → Bool) :
    ∃! a : α → Bool, s.rootValues a = roots ∧ Satisfies a s.formula :=
  s.circuit.existsUnique_signed_extension s.identity s.phase roots

theorem root_identification (s : CheckedSelection α) (a : α → Bool)
    (i : Fin s.rootCount) :
    s.rootValues a i = (a (s.identity (s.circuit.rootIndex i)) ==
      s.phase (s.circuit.rootIndex i)) := rfl

/-- Every row of each formula has a matching original row ID in the other.
This semantic checker permits duplicate rows and literal permutations. It does
not discharge the later clause-occurrence coverage/counting task. -/
def RowsEquivalent [DecidableEq α] (first second : Formula α) : Prop :=
  (∀ i : Fin first.clauses.size, ∃ j : Fin second.clauses.size,
    first.clauses[i].toFinset = second.clauses[j].toFinset) ∧
  (∀ j : Fin second.clauses.size, ∃ i : Fin first.clauses.size,
    second.clauses[j].toFinset = first.clauses[i].toFinset)

instance [DecidableEq α] (first second : Formula α) :
    Decidable (RowsEquivalent first second) := inferInstanceAs (Decidable (_ ∧ _))

theorem rowsEquivalent_models [DecidableEq α] {first second : Formula α}
    (rows : RowsEquivalent first second) (a : α → Bool) :
    Satisfies a first ↔ Satisfies a second := by
  constructor
  · intro model
    rw [satisfies_iff_rows]
    intro j
    obtain ⟨i, equal⟩ := rows.2 j
    exact (clauseHolds_of_toFinset_eq a equal).mpr
      ((satisfies_iff_rows a first).mp model i)
  · intro model
    rw [satisfies_iff_rows]
    intro i
    obtain ⟨j, equal⟩ := rows.1 i
    exact (clauseHolds_of_toFinset_eq a equal).mpr
      ((satisfies_iff_rows a second).mp model j)

/-- Full selection semantics follows from finite row checks, not discovery. -/
theorem checked_source_extension [DecidableEq α] (s : CheckedSelection α)
    (source : Formula α) (rows : RowsEquivalent source s.formula)
    (roots : Fin s.rootCount → Bool) :
    ∃! a : α → Bool, s.rootValues a = roots ∧ Satisfies a source := by
  obtain ⟨a, ⟨rootEq, model⟩, unique⟩ := s.existsUnique_extension roots
  refine ⟨a, ⟨rootEq, (rowsEquivalent_models rows a).mpr model⟩, ?_⟩
  intro b hb
  exact unique b ⟨hb.1, (rowsEquivalent_models rows b).mp hb.2⟩

end CheckedSelection

end Controller.Recognition
