module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.Rules
public import Mathlib.Data.List.Count
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Nodup

@[expose] public section

/-!
# Stored positive occurrences and counted assignments

Rules, variable values, positive counts, and occurrence buckets use finite
indexed arrays. A false transition traverses the stored occurrence list of
one variable. The count invariant compares this update with rule semantics.
-/

namespace Controller.Horn.Worklist

/-- A fixed array of normalized rules on a fixed finite variable namespace. -/
abbrev RuleTable (n m : Nat) := Vector (Rule (Fin n)) m

/-- Distinct positive labels are required for one decrement per incident row. -/
def Normalized (rules : RuleTable n m) : Prop :=
  ∀ row : Fin m, (rules[row.val]).positives.Nodup

/-- The rule compiler packaged with its unchanged row count. -/
def normalizedTable (formula : CNF.Formula (Fin n)) : RuleTable n formula.clauses.size :=
  ⟨compileFormula formula, compileFormula_size formula⟩

theorem normalizedTable_normalized (formula : CNF.Formula (Fin n)) :
    Normalized (normalizedTable formula) := by
  intro row
  simp only [normalizedTable, Vector.getElem_mk, compileFormula, Array.getElem_map]
  exact compileClause_positives_nodup formula.clauses[row.val]

/-- Each positive occurrence retains both the variable and the input row identifier. -/
def positiveIncidences (rules : RuleTable n m) : List (Fin n × Fin m) :=
  (List.finRange m).flatMap fun row =>
    (rules[row.val]).positives.map fun label => (label, row)

@[simp] theorem mem_positiveIncidences (rules : RuleTable n m)
    (label : Fin n) (row : Fin m) :
    (label, row) ∈ positiveIncidences rules ↔ label ∈ (rules[row.val]).positives := by
  simp [positiveIncidences, List.mem_flatMap, List.mem_map]

theorem positiveIncidences_nodup (rules : RuleTable n m) (normalized : Normalized rules) :
    (positiveIncidences rules).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro row _
    exact (normalized row).map (fun _ _ equal => (Prod.mk.inj equal).1)
  · apply (List.nodup_finRange m).imp
    intro first second distinct edge firstMember secondMember
    obtain ⟨firstLabel, _, firstEquation⟩ := List.mem_map.mp firstMember
    obtain ⟨secondLabel, _, secondEquation⟩ := List.mem_map.mp secondMember
    exact distinct ((Prod.mk.inj (firstEquation.trans secondEquation.symm)).2)

/-- Build stored buckets by one traversal of the incidence list. -/
def bucketIncidences : List (Fin n × Fin m) → Vector (List (Fin m)) n
  | [] => Vector.replicate n []
  | (label, row) :: rest =>
      let table := bucketIncidences rest
      table.set label.val (row :: table[label.val]) label.isLt

theorem bucketIncidences_get (edges : List (Fin n × Fin m)) (label : Fin n) :
    (bucketIncidences edges)[label.val] =
      edges.filterMap (fun edge => if edge.1 = label then some edge.2 else none) := by
  induction edges with
  | nil => simp [bucketIncidences]
  | cons edge rest inductionHypothesis =>
      rcases edge with ⟨source, row⟩
      simp only [bucketIncidences, Vector.getElem_set, List.filterMap_cons]
      by_cases equal : source = label
      · subst source
        simp [inductionHypothesis]
      · have unequalValues : source.val ≠ label.val := fun same => equal (Fin.ext same)
        simp [equal, unequalValues, inductionHypothesis]

@[simp] theorem mem_bucketIncidences (edges : List (Fin n × Fin m))
    (label : Fin n) (row : Fin m) :
    row ∈ (bucketIncidences edges)[label.val] ↔ (label, row) ∈ edges := by
  rw [bucketIncidences_get]
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨⟨source, sourceRow⟩, member, value⟩
    dsimp at value
    split at value
    · rename_i equal
      have rowEquation : sourceRow = row := Option.some.inj value
      simpa [equal, rowEquation] using member
    · contradiction
  · intro member
    exact ⟨(label, row), member, by simp⟩

theorem bucketIncidences_nodup (edges : List (Fin n × Fin m)) (noDuplicates : edges.Nodup)
    (label : Fin n) : ((bucketIncidences edges)[label.val]).Nodup := by
  rw [bucketIncidences_get]
  apply List.Nodup.filterMap ?_ noDuplicates
  intro first second row firstValue secondValue
  rcases first with ⟨firstLabel, firstRow⟩
  rcases second with ⟨secondLabel, secondRow⟩
  simp only [Option.mem_def] at firstValue secondValue
  split at firstValue
  · rename_i firstEqual
    split at secondValue
    · rename_i secondEqual
      have firstRowEqual := Option.some.inj firstValue
      have secondRowEqual := Option.some.inj secondValue
      simp_all
    · contradiction
  · contradiction

/-- The stored row occurrences for every variable. -/
def occurrences (rules : RuleTable n m) : Vector (List (Fin m)) n :=
  bucketIncidences (positiveIncidences rules)

@[simp] theorem mem_occurrences (rules : RuleTable n m) (label : Fin n) (row : Fin m) :
    row ∈ (occurrences rules)[label.val] ↔ label ∈ (rules[row.val]).positives := by
  simp [occurrences]

theorem occurrences_nodup (rules : RuleTable n m) (normalized : Normalized rules)
    (label : Fin n) : ((occurrences rules)[label.val]).Nodup :=
  bucketIncidences_nodup _ (positiveIncidences_nodup rules normalized) label

/-- The semantic positive count under an assignment. -/
def positiveCount (rule : Rule α) (assignment : α → Bool) : Nat :=
  rule.positives.countP assignment

theorem positiveCount_eq_zero (rule : Rule α) (assignment : α → Bool) :
    positiveCount rule assignment = 0 ↔
      ∀ label ∈ rule.positives, assignment label = false := by
  simp only [positiveCount, List.countP_eq_zero, Bool.not_eq_true]

theorem positiveCount_pos (rule : Rule α) (assignment : α → Bool) :
    0 < positiveCount rule assignment ↔
      ∃ label ∈ rule.positives, assignment label = true := by
  exact List.countP_pos_iff

/-- On distinct labels, switching one variable off removes precisely its true occurrence. -/
theorem countP_forceFalse [DecidableEq α] (labels : List α) (noDuplicates : labels.Nodup)
    (assignment : α → Bool) (label : α) :
    labels.countP (forceFalse assignment label) =
      labels.countP assignment - if label ∈ labels ∧ assignment label = true then 1 else 0 := by
  calc
    labels.countP (forceFalse assignment label) = (labels.erase label).countP assignment := by
      rw [noDuplicates.erase_eq_filter, List.countP_filter]
      apply List.countP_congr
      intro current _
      by_cases equal : current = label <;> simp [forceFalse, equal]
    _ = _ := List.countP_erase assignment labels label

/-- Array values together with an independently stored positive count for each row. -/
structure CountedState (n m : Nat) where
  values : Vector Bool n
  counts : Vector Nat m

namespace CountedState

/-- Read an array value as a Boolean assignment. -/
def assignment (state : CountedState n m) : Fin n → Bool :=
  fun label => state.values[label.val]

/-- The stored counts agree with the current assignment in every row. -/
def Correct (rules : RuleTable n m) (state : CountedState n m) : Prop :=
  ∀ row : Fin m, state.counts[row.val] = positiveCount rules[row.val] state.assignment

/-- All variables initially remain true, so every count is its distinct support size. -/
def initial (rules : RuleTable n m) : CountedState n m where
  values := Vector.replicate n true
  counts := Vector.ofFn fun row => (rules[row.val]).positives.length

@[simp] theorem initial_assignment (rules : RuleTable n m) :
    (initial rules).assignment = fun _ => true := by
  funext label
  simp [assignment, initial]

theorem initial_correct (rules : RuleTable n m) : Correct rules (initial rules) := by
  intro row
  rw [initial_assignment]
  simp [initial, positiveCount]

end CountedState

/-- Decrement precisely the supplied row indices, in their stored occurrence order. -/
def decrementRows : List (Fin m) → Vector Nat m → Vector Nat m
  | [], counts => counts
  | row :: rest, counts =>
      decrementRows rest (counts.set row.val (counts[row.val] - 1) row.isLt)

theorem decrementRows_get (rows : List (Fin m)) (noDuplicates : rows.Nodup)
    (counts : Vector Nat m) (row : Fin m) :
    (decrementRows rows counts)[row.val] =
      counts[row.val] - if row ∈ rows then 1 else 0 := by
  induction rows generalizing counts with
  | nil => simp [decrementRows]
  | cons first rest inductionHypothesis =>
      obtain ⟨notMember, restNodup⟩ := List.nodup_cons.mp noDuplicates
      rw [decrementRows, inductionHypothesis restNodup, Vector.getElem_set]
      by_cases equal : first = row
      · subst first
        simp [notMember]
      · have unequalValues : first.val ≠ row.val := fun same => equal (Fin.ext same)
        simp [Ne.symm equal, unequalValues]

namespace CountedState

/-- A first-false transition reads only one precomputed occurrence bucket. -/
def turnOff (index : Vector (List (Fin m)) n) (state : CountedState n m)
    (label : Fin n) : CountedState n m where
  values := state.values.set label.val false label.isLt
  counts := decrementRows index[label.val] state.counts

@[simp] theorem turnOff_assignment (index : Vector (List (Fin m)) n)
    (state : CountedState n m) (label : Fin n) :
    (turnOff index state label).assignment = forceFalse state.assignment label := by
  funext current
  simp only [assignment, turnOff, Vector.getElem_set, forceFalse]
  by_cases equal : current = label
  · subst current
    simp
  · have unequalValues : label.val ≠ current.val :=
      fun same => equal (Fin.ext same.symm)
    simp [equal, unequalValues]

/-- The stored counts remain exact after the first false transition of a variable. -/
theorem turnOff_correct (rules : RuleTable n m) (normalized : Normalized rules)
    (state : CountedState n m) (correct : state.Correct rules) (label : Fin n)
    (wasTrue : state.assignment label = true) :
    (turnOff (occurrences rules) state label).Correct rules := by
  intro row
  rw [show (turnOff (occurrences rules) state label).counts =
    decrementRows (occurrences rules)[label.val] state.counts from rfl]
  rw [decrementRows_get _ (occurrences_nodup rules normalized label), correct row,
    turnOff_assignment]
  unfold positiveCount
  rw [countP_forceFalse _ (normalized row)]
  simp [wasTrue]

end CountedState

end Controller.Horn.Worklist
