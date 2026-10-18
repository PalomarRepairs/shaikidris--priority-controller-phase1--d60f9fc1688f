module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.Rows
public import Controller.Native.BoundedEncode
public import Controller.Resolution.Cases
public import Mathlib.Data.List.FinRange

@[expose] public section
set_option Elab.async false

/-! Constructive binary-fold projection components retain actual clause IDs and
stronger normalized subclauses. Directional prefixes share one resolution merge
per fold link. Original rows are drawn from the binary expansion's ordered
producer blocks; no named high-fanin clause is inserted as an input premise. -/
namespace Controller.NativeProof.FoldProjection
open Controller.CNF Controller.Resolution Controller.Resolution.RUP Controller.Resolution.Cases


variable {v : ℕ} {state : State v} {initial : State v} {target : Clause (Fin v)} {oldTarget : Clause (Fin v)} {arity : ℕ}

structure AvailableSubclause (state : State v) (target : Clause (Fin v)) where
  clause : Clause (Fin v)
  row : Rows.Available state clause
  subset : ClauseSubset clause target

def ofRow (row : Rows.Available state target) : AvailableSubclause state target :=
  ⟨target, row, fun _ member => member⟩

/-- A fold link joins the already shared prefix implication with an original
binary gate's directional row. Missing pivots reuse the stronger parent. -/
def implicationMerge (state : State v) (context : Clause (Fin v))
    (output previous input : Literal (Fin v))
    (link : AvailableSubclause state [negate previous, input])
    (prefixRow : AvailableSubclause state (context ++ [negate output, previous])) : CompiledTrail v :=
  merge state link.row.id prefixRow.row.id previous link.clause prefixRow.clause

theorem implicationMerge_run (state : State v) (context : Clause (Fin v))
    (output previous input : Literal (Fin v))
    (link : AvailableSubclause state [negate previous, input])
    (prefixRow : AvailableSubclause state (context ++ [negate output, previous])) :
    runSteps state (implicationMerge state context output previous input link prefixRow).steps =
      some (implicationMerge state context output previous input link prefixRow).state :=
  (merge_run state link.row.id prefixRow.row.id previous link.clause prefixRow.clause
    link.row.present prefixRow.row.present link.row.bound prefixRow.row.bound).1

def implicationMerge_result (state : State v) (context : Clause (Fin v))
    (output previous input : Literal (Fin v))
    (link : AvailableSubclause state [negate previous, input])
    (prefixRow : AvailableSubclause state (context ++ [negate output, previous])) :
    AvailableSubclause (implicationMerge state context output previous input link prefixRow).state
      (context ++ [negate output, input]) := by
  let joined := implicationMerge state context output previous input link prefixRow
  have actual := merge_run state link.row.id prefixRow.row.id previous link.clause prefixRow.clause
    link.row.present prefixRow.row.present link.row.bound prefixRow.row.bound
  refine ⟨joined.clause, ⟨joined.rowId, actual.2.1, actual.2.2⟩, ?_⟩
  apply merge_subset
  · intro literal member
    have contained := link.subset literal member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at contained
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    aesop
  · intro literal member
    have contained := prefixRow.subset literal member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at contained ⊢
    aesop

 theorem implicationMerge_count (state : State v) (context : Clause (Fin v))
    (output previous input : Literal (Fin v))
    (link : AvailableSubclause state [negate previous, input])
    (prefixRow : AvailableSubclause state (context ++ [negate output, previous])) :
    (implicationMerge state context output previous input link prefixRow).steps.length ≤ 1 :=
  merge_count_le_one state link.row.id prefixRow.row.id previous link.clause prefixRow.clause

/-- The long-clause join eliminates one binary prefix, retaining both parents'
other literals. Normalization may produce a stronger target subclause. -/
def longMerge (state : State v) (pivot : Literal (Fin v))
    (leftRest rightRest : Clause (Fin v))
    (left : AvailableSubclause state (negate pivot :: leftRest))
    (right : AvailableSubclause state (pivot :: rightRest)) : CompiledTrail v :=
  merge state left.row.id right.row.id pivot left.clause right.clause

def longMerge_result (state : State v) (pivot : Literal (Fin v))
    (leftRest rightRest : Clause (Fin v))
    (left : AvailableSubclause state (negate pivot :: leftRest))
    (right : AvailableSubclause state (pivot :: rightRest)) :
    AvailableSubclause (longMerge state pivot leftRest rightRest left right).state (leftRest ++ rightRest) := by
  let joined := longMerge state pivot leftRest rightRest left right
  have actual := merge_run state left.row.id right.row.id pivot left.clause right.clause
    left.row.present right.row.present left.row.bound right.row.bound
  refine ⟨joined.clause, ⟨joined.rowId, actual.2.1, actual.2.2⟩, ?_⟩
  apply merge_subset
  · intro literal member
    have contained := left.subset literal member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at contained ⊢
    aesop
  · intro literal member
    have contained := right.subset literal member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at contained ⊢
    aesop

 theorem longMerge_run (state : State v) (pivot : Literal (Fin v))
    (leftRest rightRest : Clause (Fin v))
    (left : AvailableSubclause state (negate pivot :: leftRest))
    (right : AvailableSubclause state (pivot :: rightRest)) :
    runSteps state (longMerge state pivot leftRest rightRest left right).steps =
      some (longMerge state pivot leftRest rightRest left right).state :=
  (merge_run state left.row.id right.row.id pivot left.clause right.clause
    left.row.present right.row.present left.row.bound right.row.bound).1

 theorem longMerge_count (state : State v) (pivot : Literal (Fin v))
    (leftRest rightRest : Clause (Fin v))
    (left : AvailableSubclause state (negate pivot :: leftRest))
    (right : AvailableSubclause state (pivot :: rightRest)) :
    (longMerge state pivot leftRest rightRest left right).steps.length ≤ 1 :=
  merge_count_le_one state left.row.id right.row.id pivot left.clause right.clause

/-- Each binary producer row is an actual occurrence in the retained expansion.
Caller frames may contain any other producer blocks or assertions. -/
def boundedOriginalRow (output : Literal α) (gate : Gate α)
    (rename : Controller.Native.Bounded.LocalVariable α
      (Controller.Native.Bounded.auxiliaryCount gate) → Fin v)
    (before after : List (Clause (Controller.Native.Bounded.LocalVariable α
      (Controller.Native.Bounded.auxiliaryCount gate))))
    (index : Fin (Controller.Native.Bounded.rows output gate).length) :
    Rows.Available (initialState (relabel rename (ofClauses
      (before ++ Controller.Native.Bounded.rows output gate ++ after))))
      (Rows.mapClause rename (Controller.Native.Bounded.rows output gate)[index.val]) :=
  Rows.framedRow rename before (Controller.Native.Bounded.rows output gate) after index

/-- Sharing directional prefix implications charges two passes through the
binary prefix links plus one pass for the long clause. -/
def projectionMergeBudget (arity : ℕ) : ℕ := 3 * (arity - 1)

 theorem projectionMergeBudget_linear : projectionMergeBudget arity ≤ 3 * arity := by
  unfold projectionMergeBudget
  omega

/-- Moving an existing stronger row through an actual accepted trace never
changes its ID or requires a weakened replacement clause. -/
def afterTrace (row : AvailableSubclause state target) (next : State v)
    (steps : List (Step v)) (checked : runSteps state steps = some next) :
    AvailableSubclause next target where
  clause := row.clause
  row := ⟨row.row.id,
    (runSteps_preserves_old_rows checked row.row.id row.row.bound).trans row.row.present,
    row.row.bound.trans (runSteps_lastId_le checked)⟩
  subset := row.subset

/-- These are the three actual rows of one binary conjunction producer. -/
structure BinaryAndRows (state : State v) (left right output : Literal (Fin v)) where
  leftRow : Rows.Available state [negate output, left]
  rightRow : Rows.Available state [negate output, right]
  longRow : Rows.Available state [output, negate left, negate right]

/-- A prefix chain retains the original rows for every binary producer. -/
inductive AndFold (state : State v) : Literal (Fin v) → List (Literal (Fin v)) → Type
  | pair (left right output : Literal (Fin v)) (rows : BinaryAndRows state left right output) :
      AndFold state output [left, right]
  | snoc {previous : Literal (Fin v)} {inputs : List (Literal (Fin v))}
      (prefixFold : AndFold state previous inputs) (input output : Literal (Fin v))
      (rows : BinaryAndRows state previous input output) : AndFold state output (inputs ++ [input])

def AndFold.links {output : Literal (Fin v)} {inputs : List (Literal (Fin v))} : AndFold state output inputs → ℕ
  | .pair .. => 0
  | .snoc fold _ _ _ => fold.links + 1

theorem AndFold.links_eq (fold : AndFold state output inputs) : fold.links + 2 = inputs.length := by
  induction fold with
  | pair => rfl
  | snoc fold input output rows ih => simp only [AndFold.links, List.length_append, List.length_cons, List.length_nil]; omega

structure LongProjection (initial : State v) (output : Literal (Fin v))
    (inputs : List (Literal (Fin v))) (budget : ℕ) where
  state : State v
  steps : List (Step v)
  checked : runSteps initial steps = some state
  result : AvailableSubclause state (output :: inputs.map negate)
  count : steps.length ≤ budget

/-- One original binary producer extends an already checked aggregate trace. -/
def projectLongStep (previous input output : Literal (Fin v)) (inputs : List (Literal (Fin v)))
    (budget : ℕ) (rows : BinaryAndRows state previous input output)
    (ih : LongProjection state previous inputs budget) :
    LongProjection state output (inputs ++ [input]) (budget + 1) := by
  let original := afterTrace (ofRow rows.longRow) ih.state ih.steps ih.checked
  have leftSubset : ClauseSubset original.clause (negate previous :: [output, negate input]) := by
    intro literal member
    have contained := original.subset literal member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at contained ⊢
    aesop
  let left : AvailableSubclause ih.state (negate previous :: [output, negate input]) :=
    ⟨original.clause, original.row, leftSubset⟩
  let joined := longMerge ih.state previous [output, negate input] (inputs.map negate) left ih.result
  let projected := longMerge_result ih.state previous [output, negate input] (inputs.map negate) left ih.result
  have subset : ClauseSubset projected.clause (output :: (inputs ++ [input]).map negate) := by
    intro literal member
    have contained := projected.subset literal member
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at contained ⊢
    aesop
  refine ⟨joined.state, ih.steps ++ joined.steps, ?_,
    ⟨projected.clause, projected.row, subset⟩, ?_⟩
  · simp only [runSteps_append, ih.checked, Option.bind_some]
    exact longMerge_run ih.state previous [output, negate input] (inputs.map negate) left ih.result
  · have localCount := longMerge_count ih.state previous [output, negate input] (inputs.map negate) left ih.result
    simp only [List.length_append]
    have oldCount := ih.count
    dsimp only [joined] at ⊢
    omega

/-- Forward traversal computes each private prefix once. Subset and count
proofs reside in the nonrecursive step constructor. -/
def projectLong {output : Literal (Fin v)} {inputs : List (Literal (Fin v))}
    (fold : AndFold state output inputs) : LongProjection state output inputs fold.links :=
  match fold with
  | .pair _ _ _ rows => ⟨state, [], rfl, ofRow rows.longRow, by simp [AndFold.links]⟩
  | @AndFold.snoc _ _ previous inputs chain input output rows =>
      projectLongStep previous input output inputs chain.links rows (projectLong chain)

/-- Uniform count for the actual long-clause traversal, including duplicate
input occurrences and arbitrary signed literals. -/
theorem projectLong_linear (fold : AndFold state output inputs) :
    (projectLong fold).steps.length ≤ inputs.length - 2 := by
  have count := (projectLong fold).count
  have size := fold.links_eq
  omega

structure InputProjection (initial : State v) (root : Literal (Fin v))
    (inputs : List (Literal (Fin v))) (budget : ℕ) where
  state : State v
  steps : List (Step v)
  checked : runSteps initial steps = some state
  results : ∀ input ∈ inputs, AvailableSubclause state [negate root, input]
  count : steps.length ≤ budget

/-- A shared directional prefix is extended to both inputs of a single binary
producer. Original rows are transported through the accepted prefix. -/
def descendCell (initial current : State v) (prefixSteps : List (Step v))
    (checked : runSteps initial prefixSteps = some current)
    (root left right output : Literal (Fin v))
    (rows : BinaryAndRows initial left right output)
    (prefixRow : AvailableSubclause current [negate root, output]) :
    InputProjection current root [left, right] 2 := by
  let leftLink := afterTrace (ofRow rows.leftRow) current prefixSteps checked
  let first := implicationMerge current [] root output left leftLink prefixRow
  let leftResult := implicationMerge_result current [] root output left leftLink prefixRow
  have firstRun := implicationMerge_run current [] root output left leftLink prefixRow
  let nextPrefix := afterTrace prefixRow first.state first.steps firstRun
  have nextChecked : runSteps initial (prefixSteps ++ first.steps) = some first.state := by
    simp only [runSteps_append, checked, Option.bind_some]; exact firstRun
  let rightLink := afterTrace (ofRow rows.rightRow) first.state (prefixSteps ++ first.steps) nextChecked
  let second := implicationMerge first.state [] root output right rightLink nextPrefix
  let rightResult := implicationMerge_result first.state [] root output right rightLink nextPrefix
  have secondRun := implicationMerge_run first.state [] root output right rightLink nextPrefix
  let finalLeft := afterTrace leftResult second.state second.steps secondRun
  refine ⟨second.state, first.steps ++ second.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append]
    have firstChecked : runSteps current first.steps = some first.state := firstRun
    rw [firstChecked]
    exact secondRun
  · intro input member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    if same : input = left then
      subst input; exact finalLeft
    else
      have rightSame : input = right := member.resolve_left same
      subst input; exact rightResult
  · have firstCount := implicationMerge_count current [] root output left leftLink prefixRow
    have secondCount := implicationMerge_count first.state [] root output right rightLink nextPrefix
    change first.steps.length ≤ 1 at firstCount
    change second.steps.length ≤ 1 at secondCount
    simp only [List.length_append]
    omega

/-- Assemble two accepted directional traversals without expanding their proofs
inside the recursive fold equations. -/
def appendInputProjection (root previous input : Literal (Fin v))
    (inputs : List (Literal (Fin v))) (links : ℕ)
    (localResult : InputProjection state root [previous, input] 2)
    (recursive : InputProjection localResult.state root inputs (2 * (links + 1))) :
    InputProjection state root (inputs ++ [input]) (2 * ((links + 1) + 1)) := by
  let finalInput := afterTrace (localResult.results input (by simp))
    recursive.state recursive.steps recursive.checked
  refine ⟨recursive.state, localResult.steps ++ recursive.steps, ?_, ?_, ?_⟩
  · simp only [runSteps_append, localResult.checked, Option.bind_some]
    exact recursive.checked
  · intro vertex member
    if old : vertex ∈ inputs then
      exact recursive.results vertex old
    else
      have last := (List.mem_append.mp member).resolve_left old
      have same : vertex = input := by simpa using last
      subst vertex
      exact finalInput
  · have localCount := localResult.count
    have recursiveCount := recursive.count
    simp only [List.length_append]
    omega

/-- Downward traversal reuses each output-to-prefix implication once. It emits
at most two merges per binary producer rather than replaying every full path. -/
def projectInputsBelow (fold : AndFold initial output inputs) (current : State v)
    (prefixSteps : List (Step v)) (checked : runSteps initial prefixSteps = some current)
    (root : Literal (Fin v)) (prefixRow : AvailableSubclause current [negate root, output]) :
    InputProjection current root inputs (2 * (fold.links + 1)) := by
  match fold with
  | .pair left right output rows =>
    exact descendCell initial current prefixSteps checked root left right output rows prefixRow
  | @AndFold.snoc _ _ previous inputs fold input output rows =>
    let localResult : InputProjection current root [previous, input] 2 :=
      descendCell initial current prefixSteps checked root previous input output rows prefixRow
    have allChecked : runSteps initial (prefixSteps ++ localResult.steps) = some localResult.state := by
      simp only [runSteps_append, checked, Option.bind_some]
      exact localResult.checked
    let nextPrefix := localResult.results previous (by simp)
    let recursive := projectInputsBelow fold localResult.state (prefixSteps ++ localResult.steps)
      allChecked root nextPrefix
    exact appendInputProjection root previous input inputs fold.links localResult recursive

/-- The top binary producer already supplies both output implications. The
backward pass starts from those actual original rows, never a tautology axiom. -/
def projectInputs (fold : AndFold state output inputs) :
    InputProjection state output inputs (2 * fold.links) := by
  cases fold with
  | pair left right output rows =>
    refine ⟨state, [], rfl, ?_, by simp [AndFold.links]⟩
    intro input member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    if same : input = left then
      subst input; exact ofRow rows.leftRow
    else
      have rightSame : input = right := member.resolve_left same
      subst input; exact ofRow rows.rightRow
  | @snoc previous oldInputs fold input output rows =>
    let recursive := projectInputsBelow fold state [] rfl output (ofRow rows.leftRow)
    let finalInput := afterTrace (ofRow rows.rightRow) recursive.state recursive.steps recursive.checked
    refine ⟨recursive.state, recursive.steps, recursive.checked, ?_, ?_⟩
    · intro vertex member
      if old : vertex ∈ oldInputs then
        exact recursive.results vertex old
      else
        have last := (List.mem_append.mp member).resolve_left old
        have same : vertex = input := by simpa using last
        subst vertex; exact finalInput
    · exact recursive.count

 theorem projectInputs_linear (fold : AndFold state output inputs) :
    (projectInputs fold).steps.length ≤ 2 * (inputs.length - 2) := by
  have count := (projectInputs fold).count
  have size := fold.links_eq
  omega

def BinaryAndRows.afterTrace (rows : BinaryAndRows state left right output)
    (next : State v) (steps : List (Step v)) (checked : runSteps state steps = some next) :
    BinaryAndRows next left right output where
  leftRow := (Controller.NativeProof.FoldProjection.afterTrace (ofRow rows.leftRow) next steps checked).row
  rightRow := (Controller.NativeProof.FoldProjection.afterTrace (ofRow rows.rightRow) next steps checked).row
  longRow := (Controller.NativeProof.FoldProjection.afterTrace (ofRow rows.longRow) next steps checked).row

def AndFold.afterTrace (fold : AndFold state output inputs)
    (next : State v) (steps : List (Step v)) (checked : runSteps state steps = some next) :
    AndFold next output inputs :=
  match fold with
  | .pair left right output rows => .pair left right output (rows.afterTrace next steps checked)
  | .snoc previous input output rows =>
      .snoc (previous.afterTrace next steps checked) input output (rows.afterTrace next steps checked)

theorem AndFold.afterTrace_links (fold : AndFold state output inputs)
    (next : State v) (steps : List (Step v)) (checked : runSteps state steps = some next) :
    (fold.afterTrace next steps checked).links = fold.links := by
  induction fold <;> simp [AndFold.afterTrace, AndFold.links, *]

structure CompleteProjection (initial : State v) (clauses : List (Clause (Fin v))) (budget : ℕ) where
  state : State v
  steps : List (Step v)
  checked : runSteps initial steps = some state
  results : ∀ clause ∈ clauses, AvailableSubclause state clause
  count : steps.length ≤ budget

/-- Search the represented occurrence list by decidable equality. The returned
index witness selects runtime data; propositional membership only verifies it. -/
def mappedChoice {α β : Type} [DecidableEq β] (f : α → β) (wanted : β)
    (values : List α) (member : wanted ∈ values.map f) :
    {value : α // value ∈ values ∧ f value = wanted} :=
  match values with
  | [] => False.elim (by simp at member)
  | value :: rest =>
    if same : f value = wanted then
      ⟨value, by simp, same⟩
    else
      let selected := mappedChoice f wanted rest (by
        have alternatives : wanted = f value ∨ wanted ∈ rest.map f := by simpa using member
        exact alternatives.resolve_left (Ne.symm same))
      ⟨selected.val, List.mem_cons_of_mem value selected.property.1, selected.property.2⟩

/-- Both traversals are concatenated as actual checked ordinary-resolution
steps. Every named conjunction clause is represented by an available stronger
subclause; repeated inputs remain in the requested occurrence list. -/
def projectAnd (fold : AndFold state output inputs) :
    CompleteProjection state ((Gate.and inputs).clauses output) (3 * fold.links) := by
  let aggregate := projectLong fold
  let transported := fold.afterTrace aggregate.state aggregate.steps aggregate.checked
  let directional := projectInputs transported
  let aggregateRow := afterTrace aggregate.result directional.state directional.steps directional.checked
  refine ⟨directional.state, aggregate.steps ++ directional.steps, ?_, ?_, ?_⟩
  · simp only [runSteps_append, aggregate.checked, Option.bind_some]; exact directional.checked
  · intro clause member
    if aggregateSame : clause = output :: inputs.map negate then
      subst clause; exact aggregateRow
    else
      have directionalMem : clause ∈ inputs.map (fun input => [negate output, input]) := by
        simpa only [Gate.clauses, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false, aggregateSame, or_false] using member
      let selected := mappedChoice (fun input => [negate output, input]) clause inputs directionalMem
      exact selected.property.2 ▸ directional.results selected.val selected.property.1
  · have aggregateCount := aggregate.count
    have directionalCount := directional.count
    have links := fold.afterTrace_links aggregate.state aggregate.steps aggregate.checked
    change transported.links = fold.links at links
    simp only [List.length_append]
    change aggregate.steps.length + directional.steps.length ≤ 3 * fold.links
    omega

 theorem projectAnd_linear (fold : AndFold state output inputs) :
    (projectAnd fold).steps.length ≤ 3 * (inputs.length - 2) := by
  have count := (projectAnd fold).count
  have size := fold.links_eq
  omega

structure BinaryOrRows (state : State v) (left right output : Literal (Fin v)) where
  leftRow : Rows.Available state [output, negate left]
  rightRow : Rows.Available state [output, negate right]
  longRow : Rows.Available state [negate output, left, right]

def BinaryOrRows.dual (rows : BinaryOrRows state left right output) :
    BinaryAndRows state (negate left) (negate right) (negate output) where
  leftRow := by simpa using rows.leftRow
  rightRow := by simpa using rows.rightRow
  longRow := by simpa using rows.longRow

inductive OrFold (state : State v) : Literal (Fin v) → List (Literal (Fin v)) → Type
  | pair (left right output : Literal (Fin v)) (rows : BinaryOrRows state left right output) :
      OrFold state output [left, right]
  | snoc {previous : Literal (Fin v)} {inputs : List (Literal (Fin v))}
      (prefixFold : OrFold state previous inputs) (input output : Literal (Fin v))
      (rows : BinaryOrRows state previous input output) : OrFold state output (inputs ++ [input])

def OrFold.dual (fold : OrFold state output inputs) : AndFold state (negate output) (inputs.map negate) := by
  match fold with
  | .pair left right output rows => exact .pair (negate left) (negate right) (negate output) rows.dual
  | .snoc previous input output rows =>
    simpa using AndFold.snoc previous.dual (negate input) (negate output) rows.dual

def projectOr (fold : OrFold state output inputs) :
    CompleteProjection state ((Gate.or inputs).clauses output) (3 * (inputs.length - 2)) := by
  let projected := projectAnd fold.dual
  refine ⟨projected.state, projected.steps, projected.checked, ?_, ?_⟩
  · intro clause member
    have dualMember : clause ∈ (Gate.and (inputs.map negate)).clauses (negate output) := by
      simpa [Gate.clauses, Function.comp_def, List.map_map] using member
    exact projected.results clause dualMember
  · have count := projected.count
    have size := fold.dual.links_eq
    simp only [List.length_map] at size
    omega

/-- Empty producers supply their unit aggregate clause directly. -/
def emptyAndProjection (row : Rows.Available state [output]) :
    CompleteProjection state ((Gate.and []).clauses output) 0 := by
  refine ⟨state, [], rfl, ?_, by simp⟩
  intro clause member
  have same : clause = [output] := by simpa [Gate.clauses, Function.comp_def, List.map_map] using member
  subst clause; exact ofRow row

def emptyOrProjection (row : Rows.Available state [negate output]) :
    CompleteProjection state ((Gate.or []).clauses output) 0 := by
  refine ⟨state, [], rfl, ?_, by simp⟩
  intro clause member
  have same : clause = [negate output] := by simpa [Gate.clauses, Function.comp_def, List.map_map] using member
  subst clause; exact ofRow row

/-- Unary binary-expansion producers are aliases, whose two original rows are
exactly the unary AND and OR equation rows. -/
def unaryAndProjection (input : Literal (Fin v))
    (forward : Rows.Available state [negate output, input])
    (backward : Rows.Available state [output, negate input]) :
    CompleteProjection state ((Gate.and [input]).clauses output) 0 := by
  refine ⟨state, [], rfl, ?_, by simp⟩
  intro clause member
  simp only [Gate.clauses, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  if same : clause = [negate output, input] then
    subst clause; exact ofRow forward
  else
    have reverseSame : clause = [output, negate input] := member.resolve_left same
    subst clause; exact ofRow backward

def unaryOrProjection (input : Literal (Fin v))
    (forward : Rows.Available state [negate output, input])
    (backward : Rows.Available state [output, negate input]) :
    CompleteProjection state ((Gate.or [input]).clauses output) 0 := by
  refine ⟨state, [], rfl, ?_, by simp⟩
  intro clause member
  simp only [Gate.clauses, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  if same : clause = [output, negate input] then
    subst clause; exact ofRow backward
  else
    have forwardSame : clause = [negate output, input] := member.resolve_left same
    subst clause; exact ofRow forward

/-- Actual expanded producer occurrences are framed by the rows of the
preceding and succeeding producers, preserving repeated clauses and IDs. -/
def boundedProducerRow (output : Literal α) (gate : Gate α)
    (rename : Controller.Native.Bounded.LocalVariable α
      (Controller.Native.Bounded.auxiliaryCount gate) → Fin v)
    (owner : Fin (Controller.Native.Bounded.expand output gate).length)
    (index : Fin ((Controller.Native.Bounded.expand output gate)[owner.val]).rows.length) :
    Rows.Available (initialState (relabel rename (ofClauses (Controller.Native.Bounded.rows output gate))))
      (Rows.mapClause rename ((Controller.Native.Bounded.expand output gate)[owner.val]).rows[index.val]) := by
  let producers := Controller.Native.Bounded.expand output gate
  let current := producers[owner.val]
  let before := (producers.take owner.val).flatMap Controller.Native.Bounded.Producer.rows
  let after := (producers.drop (owner.val + 1)).flatMap Controller.Native.Bounded.Producer.rows
  have split : Controller.Native.Bounded.rows output gate = before ++ current.rows ++ after := by
    change producers.flatMap Controller.Native.Bounded.Producer.rows = _
    have listSplit : producers = producers.take owner.val ++ current :: producers.drop (owner.val + 1) := by
      calc
        producers = producers.take owner.val ++ producers.drop owner.val := (List.take_append_drop owner.val producers).symm
        _ = producers.take owner.val ++ current :: producers.drop (owner.val + 1) :=
          congrArg (fun tail => producers.take owner.val ++ tail) (List.getElem_cons_drop owner.isLt).symm
    rw [listSplit]
    simp only [List.flatMap_append, List.flatMap_cons]
    exact (List.append_assoc before current.rows after).symm
  rw [split]
  exact Rows.framedRow rename before current.rows after index

/-- Binary gate shape binds all three directional/aggregate rows directly to
original expanded producer occurrences. It is a syntactic gate equality. -/
def boundedAndProducerRows (output : Literal α) (gate : Gate α)
    (rename : Controller.Native.Bounded.LocalVariable α
      (Controller.Native.Bounded.auxiliaryCount gate) → Fin v)
    (owner : Fin (Controller.Native.Bounded.expand output gate).length)
    (left right : Literal (Controller.Native.Bounded.LocalVariable α
      (Controller.Native.Bounded.auxiliaryCount gate)))
    (shape : ((Controller.Native.Bounded.expand output gate)[owner.val]).gate = .and [left, right]) :
    BinaryAndRows (initialState (relabel rename (ofClauses (Controller.Native.Bounded.rows output gate))))
      (rename left.1, left.2) (rename right.1, right.2)
      (rename ((Controller.Native.Bounded.expand output gate)[owner.val]).output.1,
        ((Controller.Native.Bounded.expand output gate)[owner.val]).output.2) := by
  have rowCount : ((Controller.Native.Bounded.expand output gate)[owner.val]).rows.length = 3 := by
    simp [Controller.Native.Bounded.Producer.rows, shape, Gate.clauses]
  refine ⟨?_, ?_, ?_⟩
  · have actual := boundedProducerRow output gate rename owner ⟨0, by omega⟩
    simpa [Controller.Native.Bounded.Producer.rows, shape, Gate.clauses, Rows.mapClause, negate, Std.Sat.Literal.negate] using actual
  · have actual := boundedProducerRow output gate rename owner ⟨1, by omega⟩
    simpa [Controller.Native.Bounded.Producer.rows, shape, Gate.clauses, Rows.mapClause, negate, Std.Sat.Literal.negate] using actual
  · have actual := boundedProducerRow output gate rename owner ⟨2, by omega⟩
    simpa [Controller.Native.Bounded.Producer.rows, shape, Gate.clauses, Rows.mapClause, negate, Std.Sat.Literal.negate] using actual

def mappedLiteral (rename : α → Fin v) (literal : Literal α) : Literal (Fin v) :=
  (rename literal.1, literal.2)

def foldFirst (inputs : List (Literal α)) (atLeastTwo : 2 ≤ inputs.length)
    (index : Fin (inputs.length - 1)) :
    Literal (Controller.Native.Bounded.LocalVariable α (inputs.length - 2)) :=
  if first : index.val = 0 then
    Controller.Native.Bounded.originalLiteral (inputs.get ⟨0, by omega⟩)
  else (.auxiliary ⟨index.val - 1, by have := index.isLt; omega⟩, true)

def foldSecond (inputs : List (Literal α)) (atLeastTwo : 2 ≤ inputs.length)
    (index : Fin (inputs.length - 1)) :
    Literal (Controller.Native.Bounded.LocalVariable α (inputs.length - 2)) :=
  Controller.Native.Bounded.originalLiteral (inputs.get ⟨index.val + 1, by have := index.isLt; omega⟩)

def foldOwner (inputs : List (Literal α)) (output : Literal α)
    (atLeastTwo : 2 ≤ inputs.length) (index : Fin (inputs.length - 1)) :
    Fin (Controller.Native.Bounded.expand output (.and inputs)).length :=
  ⟨index.val, by
    change index.val < (Controller.Native.Bounded.foldProducers .conjunction inputs output).length
    rw [Controller.Native.Bounded.foldProducers_length]
    unfold Controller.Native.Bounded.foldProducerCount
    rw [Nat.max_eq_right (show 1 ≤ inputs.length - 1 by omega)]
    exact index.isLt⟩

theorem foldProducer_shape (inputs : List (Literal α)) (output : Literal α)
    (atLeastTwo : 2 ≤ inputs.length) (index : Fin (inputs.length - 1)) :
    (Controller.Native.Bounded.expand output (.and inputs))[ (foldOwner inputs output atLeastTwo index).val] =
      { output := Controller.Native.Bounded.foldOutput inputs output index,
        gate := .and [foldFirst inputs atLeastTwo index, foldSecond inputs atLeastTwo index] } := by
  have nonempty : inputs.length ≠ 0 := by omega
  have nonunary : inputs.length ≠ 1 := by omega
  let normalized : List (Controller.Native.Bounded.Producer
      (Controller.Native.Bounded.LocalVariable α (inputs.length - 2))) :=
    (List.finRange (inputs.length - 1)).map fun slot =>
      { output := Controller.Native.Bounded.foldOutput inputs output slot,
        gate := .and [foldFirst inputs atLeastTwo slot, foldSecond inputs atLeastTwo slot] }
  have whole : Controller.Native.Bounded.foldProducers .conjunction inputs output = normalized := by
    unfold Controller.Native.Bounded.foldProducers
    rw [dite_eq_right nonempty, dite_eq_right nonunary]
    rfl
  have valid : index.val < (Controller.Native.Bounded.foldProducers .conjunction inputs output).length :=
    (foldOwner inputs output atLeastTwo index).isLt
  have normalizedValid : index.val < normalized.length := by
    simpa only [normalized, List.length_map, List.length_finRange] using index.isLt
  have lookup := congrArg (fun producers => producers[index.val]?) whole
  rw [List.getElem?_eq_getElem valid, List.getElem?_eq_getElem normalizedValid] at lookup
  have content : normalized[index.val]'normalizedValid =
      { output := Controller.Native.Bounded.foldOutput inputs output index,
        gate := .and [foldFirst inputs atLeastTwo index, foldSecond inputs atLeastTwo index] } := by
    dsimp only [normalized]
    rw [List.getElem_map, List.getElem_finRange]
    rfl
  exact (Option.some.inj lookup).trans content

def foldCellRows (inputs : List (Literal α)) (output : Literal α)
    (atLeastTwo : 2 ≤ inputs.length)
    (rename : Controller.Native.Bounded.LocalVariable α (inputs.length - 2) → Fin v)
    (index : Fin (inputs.length - 1)) :
    BinaryAndRows (initialState (relabel rename (ofClauses (Controller.Native.Bounded.rows output (.and inputs)))))
      (mappedLiteral rename (foldFirst inputs atLeastTwo index))
      (mappedLiteral rename (foldSecond inputs atLeastTwo index))
      (mappedLiteral rename (Controller.Native.Bounded.foldOutput inputs output index)) := by
  with_unfolding_all
    try dsimp only [Controller.Native.Bounded.auxiliaryCount] at ⊢
    have actual := boundedAndProducerRows output (.and inputs) rename
      (foldOwner inputs output atLeastTwo index) (foldFirst inputs atLeastTwo index)
      (foldSecond inputs atLeastTwo index)
      (by simp only [foldProducer_shape])
    have mappedOutput := congrArg
      (fun producer : Controller.Native.Bounded.Producer
          (Controller.Native.Bounded.LocalVariable α (inputs.length - 2)) => mappedLiteral rename producer.output)
      (foldProducer_shape inputs output atLeastTwo index)
    change mappedLiteral rename ((Controller.Native.Bounded.expand output (.and inputs))[
      (foldOwner inputs output atLeastTwo index).val]).output =
      mappedLiteral rename (Controller.Native.Bounded.foldOutput inputs output index) at mappedOutput
    rw [← mappedOutput]
    exact actual

/-- This constructor obtains every binary link from the exact producer
occurrence in `Bounded.foldProducers`, rather than supplied derived prefixes. -/
def boundedFoldPrefix (inputs : List (Literal α)) (output : Literal α)
    (atLeastTwo : 2 ≤ inputs.length)
    (rename : Controller.Native.Bounded.LocalVariable α (inputs.length - 2) → Fin v)
    (position : ℕ) (bound : position < inputs.length - 1) :
    AndFold (initialState (relabel rename (ofClauses (Controller.Native.Bounded.rows output (.and inputs)))))
      (mappedLiteral rename (Controller.Native.Bounded.foldOutput inputs output ⟨position, bound⟩))
      ((inputs.take (position + 2)).map fun literal => mappedLiteral rename (Controller.Native.Bounded.originalLiteral literal)) := by
  with_unfolding_all
    try dsimp only [Controller.Native.Bounded.auxiliaryCount] at ⊢
    induction position with
    | zero =>
      have rows := foldCellRows inputs output atLeastTwo rename ⟨0, bound⟩
      have firstTwo : inputs.take 2 = [inputs[0]'(by omega), inputs[1]'(by omega)] := by
        cases inputs with
        | nil => simp at atLeastTwo
        | cons first rest => cases rest with
          | nil => simp at atLeastTwo
          | cons second tail => rfl
      simpa [foldFirst, foldSecond, firstTwo] using
        AndFold.pair (mappedLiteral rename (foldFirst inputs atLeastTwo ⟨0, bound⟩))
          (mappedLiteral rename (foldSecond inputs atLeastTwo ⟨0, bound⟩))
          (mappedLiteral rename (Controller.Native.Bounded.foldOutput inputs output ⟨0, bound⟩)) rows
    | succ position ih =>
      have previousBound : position < inputs.length - 1 := by omega
      let previous := ih previousBound
      have rows := foldCellRows inputs output atLeastTwo rename ⟨position + 1, bound⟩
      have leftEquality : mappedLiteral rename (foldFirst inputs atLeastTwo ⟨position + 1, bound⟩) =
          mappedLiteral rename (Controller.Native.Bounded.foldOutput inputs output ⟨position, previousBound⟩) := by
        simp [foldFirst, Controller.Native.Bounded.foldOutput, show position < inputs.length - 2 by omega]
      have adapted : BinaryAndRows _
          (mappedLiteral rename (Controller.Native.Bounded.foldOutput inputs output ⟨position, previousBound⟩))
          (mappedLiteral rename (foldSecond inputs atLeastTwo ⟨position + 1, bound⟩))
          (mappedLiteral rename (Controller.Native.Bounded.foldOutput inputs output ⟨position + 1, bound⟩)) :=
        leftEquality ▸ rows
      have extended := AndFold.snoc previous
        (mappedLiteral rename (foldSecond inputs atLeastTwo ⟨position + 1, bound⟩))
        (mappedLiteral rename (Controller.Native.Bounded.foldOutput inputs output ⟨position + 1, bound⟩)) adapted
      have takeStep := List.take_append_getElem (l := inputs) (i := position + 2) (by omega)
      rw [← takeStep]
      simpa only [foldSecond, List.get_eq_getElem, List.map_append, List.map_cons, List.map_nil, Nat.add_assoc] using extended

/-- The last binary prefix is exactly the principal output slot. -/
def boundedAndFold (inputs : List (Literal α)) (output : Literal α)
    (atLeastTwo : 2 ≤ inputs.length)
    (rename : Controller.Native.Bounded.LocalVariable α (inputs.length - 2) → Fin v) :
    AndFold (initialState (relabel rename (ofClauses (Controller.Native.Bounded.rows output (.and inputs)))))
      (mappedLiteral rename (Controller.Native.Bounded.originalLiteral output))
      (inputs.map fun literal => mappedLiteral rename (Controller.Native.Bounded.originalLiteral literal)) := by
  with_unfolding_all
    try dsimp only [Controller.Native.Bounded.auxiliaryCount] at ⊢
    have actual := boundedFoldPrefix inputs output atLeastTwo rename (inputs.length - 2) (by omega)
    simpa [Controller.Native.Bounded.foldOutput,
      show inputs.length - 2 + 2 = inputs.length by omega] using actual

/-- Actual bounded original rows produce every named conjunction equation
clause with a checked linear-length ordinary-resolution trace. -/
def boundedAndProjection (inputs : List (Literal α)) (output : Literal α)
    (atLeastTwo : 2 ≤ inputs.length)
    (rename : Controller.Native.Bounded.LocalVariable α (inputs.length - 2) → Fin v) :
    CompleteProjection (initialState (relabel rename (ofClauses (Controller.Native.Bounded.rows output (.and inputs)))))
      ((Gate.and (inputs.map fun literal => mappedLiteral rename (Controller.Native.Bounded.originalLiteral literal))).clauses
        (mappedLiteral rename (Controller.Native.Bounded.originalLiteral output)))
      (3 * (inputs.length - 2)) := by
  with_unfolding_all
    let fold := boundedAndFold inputs output atLeastTwo rename
    let projected := projectAnd fold
    have size := fold.links_eq
    refine ⟨projected.state, projected.steps, projected.checked, projected.results, ?_⟩
    have count := projected.count
    simp only [List.length_map] at size
    omega

/-- Binary gate shape binds all three directional/aggregate rows directly to
original expanded producer occurrences. It is a syntactic gate equality. -/
def boundedOrProducerRows (output : Literal α) (gate : Gate α)
    (rename : Controller.Native.Bounded.LocalVariable α
      (Controller.Native.Bounded.auxiliaryCount gate) → Fin v)
    (owner : Fin (Controller.Native.Bounded.expand output gate).length)
    (left right : Literal (Controller.Native.Bounded.LocalVariable α
      (Controller.Native.Bounded.auxiliaryCount gate)))
    (shape : ((Controller.Native.Bounded.expand output gate)[owner.val]).gate = .or [left, right]) :
    BinaryOrRows (initialState (relabel rename (ofClauses (Controller.Native.Bounded.rows output gate))))
      (rename left.1, left.2) (rename right.1, right.2)
      (rename ((Controller.Native.Bounded.expand output gate)[owner.val]).output.1,
        ((Controller.Native.Bounded.expand output gate)[owner.val]).output.2) := by
  have rowCount : ((Controller.Native.Bounded.expand output gate)[owner.val]).rows.length = 3 := by
    simp [Controller.Native.Bounded.Producer.rows, shape, Gate.clauses]
  refine ⟨?_, ?_, ?_⟩
  · have actual := boundedProducerRow output gate rename owner ⟨0, by omega⟩
    simpa [Controller.Native.Bounded.Producer.rows, shape, Gate.clauses, Rows.mapClause, negate, Std.Sat.Literal.negate] using actual
  · have actual := boundedProducerRow output gate rename owner ⟨1, by omega⟩
    simpa [Controller.Native.Bounded.Producer.rows, shape, Gate.clauses, Rows.mapClause, negate, Std.Sat.Literal.negate] using actual
  · have actual := boundedProducerRow output gate rename owner ⟨2, by omega⟩
    simpa [Controller.Native.Bounded.Producer.rows, shape, Gate.clauses, Rows.mapClause, negate, Std.Sat.Literal.negate] using actual

def orFoldOwner (inputs : List (Literal α)) (output : Literal α)
    (atLeastTwo : 2 ≤ inputs.length) (index : Fin (inputs.length - 1)) :
    Fin (Controller.Native.Bounded.expand output (.or inputs)).length :=
  ⟨index.val, by
    change index.val < (Controller.Native.Bounded.foldProducers .disjunction inputs output).length
    rw [Controller.Native.Bounded.foldProducers_length]
    unfold Controller.Native.Bounded.foldProducerCount
    rw [Nat.max_eq_right (show 1 ≤ inputs.length - 1 by omega)]
    exact index.isLt⟩

theorem orFoldProducer_shape (inputs : List (Literal α)) (output : Literal α)
    (atLeastTwo : 2 ≤ inputs.length) (index : Fin (inputs.length - 1)) :
    (Controller.Native.Bounded.expand output (.or inputs))[ (orFoldOwner inputs output atLeastTwo index).val] =
      { output := Controller.Native.Bounded.foldOutput inputs output index,
        gate := .or [foldFirst inputs atLeastTwo index, foldSecond inputs atLeastTwo index] } := by
  have nonempty : inputs.length ≠ 0 := by omega
  have nonunary : inputs.length ≠ 1 := by omega
  let normalized : List (Controller.Native.Bounded.Producer
      (Controller.Native.Bounded.LocalVariable α (inputs.length - 2))) :=
    (List.finRange (inputs.length - 1)).map fun slot =>
      { output := Controller.Native.Bounded.foldOutput inputs output slot,
        gate := .or [foldFirst inputs atLeastTwo slot, foldSecond inputs atLeastTwo slot] }
  have whole : Controller.Native.Bounded.foldProducers .disjunction inputs output = normalized := by
    unfold Controller.Native.Bounded.foldProducers
    rw [dite_eq_right nonempty, dite_eq_right nonunary]
    rfl
  have valid : index.val < (Controller.Native.Bounded.foldProducers .disjunction inputs output).length :=
    (orFoldOwner inputs output atLeastTwo index).isLt
  have normalizedValid : index.val < normalized.length := by
    simpa only [normalized, List.length_map, List.length_finRange] using index.isLt
  have lookup := congrArg (fun producers => producers[index.val]?) whole
  rw [List.getElem?_eq_getElem valid, List.getElem?_eq_getElem normalizedValid] at lookup
  have content : normalized[index.val]'normalizedValid =
      { output := Controller.Native.Bounded.foldOutput inputs output index,
        gate := .or [foldFirst inputs atLeastTwo index, foldSecond inputs atLeastTwo index] } := by
    dsimp only [normalized]
    rw [List.getElem_map, List.getElem_finRange]
    rfl
  exact (Option.some.inj lookup).trans content

def orFoldCellRows (inputs : List (Literal α)) (output : Literal α)
    (atLeastTwo : 2 ≤ inputs.length)
    (rename : Controller.Native.Bounded.LocalVariable α (inputs.length - 2) → Fin v)
    (index : Fin (inputs.length - 1)) :
    BinaryOrRows (initialState (relabel rename (ofClauses (Controller.Native.Bounded.rows output (.or inputs)))))
      (mappedLiteral rename (foldFirst inputs atLeastTwo index))
      (mappedLiteral rename (foldSecond inputs atLeastTwo index))
      (mappedLiteral rename (Controller.Native.Bounded.foldOutput inputs output index)) := by
  with_unfolding_all
    try dsimp only [Controller.Native.Bounded.auxiliaryCount] at ⊢
    have actual := boundedOrProducerRows output (.or inputs) rename
      (orFoldOwner inputs output atLeastTwo index) (foldFirst inputs atLeastTwo index)
      (foldSecond inputs atLeastTwo index)
      (by simp only [orFoldProducer_shape])
    have mappedOutput := congrArg
      (fun producer : Controller.Native.Bounded.Producer
          (Controller.Native.Bounded.LocalVariable α (inputs.length - 2)) => mappedLiteral rename producer.output)
      (orFoldProducer_shape inputs output atLeastTwo index)
    change mappedLiteral rename ((Controller.Native.Bounded.expand output (.or inputs))[
      (orFoldOwner inputs output atLeastTwo index).val]).output =
      mappedLiteral rename (Controller.Native.Bounded.foldOutput inputs output index) at mappedOutput
    rw [← mappedOutput]
    exact actual

/-- This constructor obtains every binary link from the exact producer
occurrence in `Bounded.foldProducers`, rather than supplied derived prefixes. -/
def boundedOrFoldPrefix (inputs : List (Literal α)) (output : Literal α)
    (atLeastTwo : 2 ≤ inputs.length)
    (rename : Controller.Native.Bounded.LocalVariable α (inputs.length - 2) → Fin v)
    (position : ℕ) (bound : position < inputs.length - 1) :
    OrFold (initialState (relabel rename (ofClauses (Controller.Native.Bounded.rows output (.or inputs)))))
      (mappedLiteral rename (Controller.Native.Bounded.foldOutput inputs output ⟨position, bound⟩))
      ((inputs.take (position + 2)).map fun literal => mappedLiteral rename (Controller.Native.Bounded.originalLiteral literal)) := by
  with_unfolding_all
    try dsimp only [Controller.Native.Bounded.auxiliaryCount] at ⊢
    try dsimp only [Controller.Native.Bounded.auxiliaryCount] at ⊢
    induction position with
    | zero =>
      have rows := orFoldCellRows inputs output atLeastTwo rename ⟨0, bound⟩
      have firstTwo : inputs.take 2 = [inputs[0]'(by omega), inputs[1]'(by omega)] := by
        cases inputs with
        | nil => simp at atLeastTwo
        | cons first rest => cases rest with
          | nil => simp at atLeastTwo
          | cons second tail => rfl
      simpa [foldFirst, foldSecond, firstTwo] using
        OrFold.pair (mappedLiteral rename (foldFirst inputs atLeastTwo ⟨0, bound⟩))
          (mappedLiteral rename (foldSecond inputs atLeastTwo ⟨0, bound⟩))
          (mappedLiteral rename (Controller.Native.Bounded.foldOutput inputs output ⟨0, bound⟩)) rows
    | succ position ih =>
      have previousBound : position < inputs.length - 1 := by omega
      let previous := ih previousBound
      have rows := orFoldCellRows inputs output atLeastTwo rename ⟨position + 1, bound⟩
      have leftEquality : mappedLiteral rename (foldFirst inputs atLeastTwo ⟨position + 1, bound⟩) =
          mappedLiteral rename (Controller.Native.Bounded.foldOutput inputs output ⟨position, previousBound⟩) := by
        simp [foldFirst, Controller.Native.Bounded.foldOutput, show position < inputs.length - 2 by omega]
      have adapted : BinaryOrRows _
          (mappedLiteral rename (Controller.Native.Bounded.foldOutput inputs output ⟨position, previousBound⟩))
          (mappedLiteral rename (foldSecond inputs atLeastTwo ⟨position + 1, bound⟩))
          (mappedLiteral rename (Controller.Native.Bounded.foldOutput inputs output ⟨position + 1, bound⟩)) :=
        leftEquality ▸ rows
      have extended := OrFold.snoc previous
        (mappedLiteral rename (foldSecond inputs atLeastTwo ⟨position + 1, bound⟩))
        (mappedLiteral rename (Controller.Native.Bounded.foldOutput inputs output ⟨position + 1, bound⟩)) adapted
      have takeStep := List.take_append_getElem (l := inputs) (i := position + 2) (by omega)
      rw [← takeStep]
      simpa only [foldSecond, List.get_eq_getElem, List.map_append, List.map_cons, List.map_nil, Nat.add_assoc] using extended

/-- The last binary prefix is exactly the principal output slot. -/
def boundedOrFold (inputs : List (Literal α)) (output : Literal α)
    (atLeastTwo : 2 ≤ inputs.length)
    (rename : Controller.Native.Bounded.LocalVariable α (inputs.length - 2) → Fin v) :
    OrFold (initialState (relabel rename (ofClauses (Controller.Native.Bounded.rows output (.or inputs)))))
      (mappedLiteral rename (Controller.Native.Bounded.originalLiteral output))
      (inputs.map fun literal => mappedLiteral rename (Controller.Native.Bounded.originalLiteral literal)) := by
  with_unfolding_all
    have actual := boundedOrFoldPrefix inputs output atLeastTwo rename (inputs.length - 2) (by omega)
    simpa [Controller.Native.Bounded.foldOutput,
      show inputs.length - 2 + 2 = inputs.length by omega] using actual

/-- The complete disjunction projection uses the exact original binary OR
producer rows and the polarity-dual checked traversal. -/
def boundedOrProjection (inputs : List (Literal α)) (output : Literal α)
    (atLeastTwo : 2 ≤ inputs.length)
    (rename : Controller.Native.Bounded.LocalVariable α (inputs.length - 2) → Fin v) :
    CompleteProjection (initialState (relabel rename (ofClauses (Controller.Native.Bounded.rows output (.or inputs)))))
      ((Gate.or (inputs.map fun literal => mappedLiteral rename (Controller.Native.Bounded.originalLiteral literal))).clauses
        (mappedLiteral rename (Controller.Native.Bounded.originalLiteral output)))
      (3 * (inputs.length - 2)) :=
  by simpa only [List.length_map] using projectOr (boundedOrFold inputs output atLeastTwo rename)

def boundedEmptyAnd (output : Literal α)
    (rename : Controller.Native.Bounded.LocalVariable α 0 → Fin v) :
    CompleteProjection (initialState (relabel rename (ofClauses (Controller.Native.Bounded.rows output (.and [])))))
      ((Gate.and []).clauses (mappedLiteral rename (Controller.Native.Bounded.originalLiteral output))) 0 := by
  with_unfolding_all
    try dsimp only [Controller.Native.Bounded.auxiliaryCount] at ⊢
    have actual := boundedProducerRow output (.and []) rename ⟨0, by change 0 < 1; decide⟩
      ⟨0, by change 0 < 1; decide⟩
    apply emptyAndProjection
    exact actual

def boundedUnaryAnd (output input : Literal α)
    (rename : Controller.Native.Bounded.LocalVariable α 0 → Fin v) :
    CompleteProjection (initialState (relabel rename (ofClauses (Controller.Native.Bounded.rows output (.and [input])))))
      ((Gate.and [mappedLiteral rename (Controller.Native.Bounded.originalLiteral input)]).clauses
        (mappedLiteral rename (Controller.Native.Bounded.originalLiteral output))) 0 := by
  with_unfolding_all
    try dsimp only [Controller.Native.Bounded.auxiliaryCount] at ⊢
    have first := boundedProducerRow output (.and [input]) rename
      ⟨0, by change 0 < 1; decide⟩
      ⟨0, by change 0 < 2; decide⟩
    have second := boundedProducerRow output (.and [input]) rename
      ⟨0, by change 0 < 1; decide⟩
      ⟨1, by change 1 < 2; decide⟩
    apply unaryAndProjection
    · exact first
    · exact second

def boundedEmptyOr (output : Literal α)
    (rename : Controller.Native.Bounded.LocalVariable α 0 → Fin v) :
    CompleteProjection (initialState (relabel rename (ofClauses (Controller.Native.Bounded.rows output (.or [])))))
      ((Gate.or []).clauses (mappedLiteral rename (Controller.Native.Bounded.originalLiteral output))) 0 := by
  with_unfolding_all
    try dsimp only [Controller.Native.Bounded.auxiliaryCount] at ⊢
    have actual := boundedProducerRow output (.or []) rename ⟨0, by change 0 < 1; decide⟩
      ⟨0, by change 0 < 1; decide⟩
    apply emptyOrProjection
    exact actual

def boundedUnaryOr (output input : Literal α)
    (rename : Controller.Native.Bounded.LocalVariable α 0 → Fin v) :
    CompleteProjection (initialState (relabel rename (ofClauses (Controller.Native.Bounded.rows output (.or [input])))))
      ((Gate.or [mappedLiteral rename (Controller.Native.Bounded.originalLiteral input)]).clauses
        (mappedLiteral rename (Controller.Native.Bounded.originalLiteral output))) 0 := by
  with_unfolding_all
    try dsimp only [Controller.Native.Bounded.auxiliaryCount] at ⊢
    have first := boundedProducerRow output (.or [input]) rename
      ⟨0, by change 0 < 1; decide⟩
      ⟨0, by change 0 < 2; decide⟩
    have second := boundedProducerRow output (.or [input]) rename
      ⟨0, by change 0 < 1; decide⟩
      ⟨1, by change 1 < 2; decide⟩
    apply unaryOrProjection
    · exact first
    · exact second

/-- Enlarging the requested target changes only the subset proof. The actual
row, identifier, and emitted trace remain unchanged. -/
def retarget (row : AvailableSubclause state oldTarget)
    (included : ClauseSubset oldTarget target) : AvailableSubclause state target where
  clause := row.clause
  row := row.row
  subset := fun literal member => included literal (row.subset literal member)

structure SubclauseProjection (initial : State v) (target : Clause (Fin v)) (budget : ℕ) where
  state : State v
  steps : List (Step v)
  checked : runSteps initial steps = some state
  result : AvailableSubclause state target
  count : steps.length ≤ budget

/-- Discharge the aggregate conflict using actual stronger propagation rows.
When either pivot is absent, the ordinary merger reuses the stronger parent;
there is no demand that normalization reconstruct the full requested clause. -/
def dischargeInputs (state : State v) (remaining : List (Literal (Fin v))) (target : Clause (Fin v))
    (conflict : AvailableSubclause state (remaining.map negate ++ target))
    (propagation : ∀ input ∈ remaining, AvailableSubclause state (target ++ [input])) :
    SubclauseProjection state target remaining.length := by
  induction remaining generalizing state with
  | nil => exact ⟨state, [], rfl, by simpa using conflict, by simp⟩
  | cons pivot rest ih =>
    let reason : AvailableSubclause state (pivot :: target) :=
      retarget (propagation pivot (by simp)) (by
        intro literal member
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        aesop)
    let adapted : AvailableSubclause state (negate pivot :: (rest.map negate ++ target)) := by
      simpa using conflict
    let joined := longMerge state pivot (rest.map negate ++ target) target adapted reason
    let merged := longMerge_result state pivot (rest.map negate ++ target) target adapted reason
    have checked := longMerge_run state pivot (rest.map negate ++ target) target adapted reason
    let nextConflict : AvailableSubclause joined.state (rest.map negate ++ target) :=
      retarget merged (by
        intro literal member
        simp only [List.mem_append] at member ⊢
        aesop)
    let nextPropagation : ∀ input ∈ rest, AvailableSubclause joined.state (target ++ [input]) :=
      fun input member => afterTrace (propagation input (by simp [member])) joined.state joined.steps checked
    let recursive := ih joined.state nextConflict nextPropagation
    refine ⟨recursive.state, joined.steps ++ recursive.steps, ?_, recursive.result, ?_⟩
    · rw [runSteps_append]
      have joinedChecked : runSteps state joined.steps = some joined.state := checked
      rw [joinedChecked]
      exact recursive.checked
    · have firstCount := longMerge_count state pivot (rest.map negate ++ target) target adapted reason
      have restCount := recursive.count
      simp only [List.length_cons, List.length_append]
      dsimp only [joined] at ⊢
      omega

/-- Raw source pair layers form binary trees, unlike serial bounded prefixes.
Each internal node retains its actual original binary producer rows. -/
inductive AndTree (state : State v) : Literal (Fin v) → List (Literal (Fin v)) → Type
  | leaf (input : Literal (Fin v)) : AndTree state input [input]
  | node {left right : Literal (Fin v)} {leftInputs rightInputs : List (Literal (Fin v))}
      (leftTree : AndTree state left leftInputs) (rightTree : AndTree state right rightInputs)
      (output : Literal (Fin v)) (rows : BinaryAndRows state left right output) :
      AndTree state output (leftInputs ++ rightInputs)

def AndTree.nodes {output : Literal (Fin v)} {inputs : List (Literal (Fin v))} : AndTree state output inputs → ℕ
  | .leaf _ => 0
  | .node left right _ _ => left.nodes + right.nodes + 1

theorem AndTree.nodes_leaves (tree : AndTree state output inputs) : tree.nodes + 1 = inputs.length := by
  induction tree with
  | leaf => rfl
  | node left right output rows leftIH rightIH => simp only [AndTree.nodes, List.length_append]; omega

/-- A leaf aggregate is an identity marker, not a fabricated original alias
or tautology row. Consumers skip it by literal identity. -/
inductive AggregateCertificate (state : State v) (output : Literal (Fin v)) :
    List (Literal (Fin v)) → Type
  | identity : AggregateCertificate state output [output]
  | derived {inputs : List (Literal (Fin v))}
      (row : AvailableSubclause state (output :: inputs.map negate)) : AggregateCertificate state output inputs

def AggregateCertificate.afterTrace (certificate : AggregateCertificate state output inputs)
    (next : State v) (steps : List (Step v)) (checked : runSteps state steps = some next) :
    AggregateCertificate next output inputs := by
  cases certificate with
  | identity => exact .identity
  | derived row => exact .derived (Controller.NativeProof.FoldProjection.afterTrace row next steps checked)

structure AggregateProjection (initial : State v) (output : Literal (Fin v))
    (inputs : List (Literal (Fin v))) (budget : ℕ) where
  state : State v
  steps : List (Step v)
  checked : runSteps initial steps = some state
  result : AggregateCertificate state output inputs
  count : steps.length ≤ budget

/-- An internal aggregate eliminates its child pivot; a leaf identity retains
its existing literal without emitting any clause or trace step. -/
def expandChild (state : State v) (child : Literal (Fin v)) (inputs : List (Literal (Fin v)))
    (rest : Clause (Fin v)) (parent : AvailableSubclause state (negate child :: rest))
    (childResult : AggregateCertificate state child inputs) :
    SubclauseProjection state (rest ++ inputs.map negate) 1 := by
  cases childResult with
  | identity =>
    refine ⟨state, [], rfl, retarget parent ?_, by simp⟩
    intro literal member
    simp only [List.mem_cons, List.mem_append, List.map_cons, List.map_nil, List.not_mem_nil, or_false] at member ⊢
    aesop
  | derived row =>
    let joined := longMerge state child rest (inputs.map negate) parent row
    exact ⟨joined.state, joined.steps, longMerge_run state child rest (inputs.map negate) parent row,
      longMerge_result state child rest (inputs.map negate) parent row,
      longMerge_count state child rest (inputs.map negate) parent row⟩

def AndTree.afterTrace (tree : AndTree state output inputs)
    (next : State v) (steps : List (Step v)) (checked : runSteps state steps = some next) :
    AndTree next output inputs :=
  match tree with
  | .leaf input => .leaf input
  | .node left right output rows =>
      .node (left.afterTrace next steps checked) (right.afterTrace next steps checked)
        output (rows.afterTrace next steps checked)

theorem AndTree.afterTrace_nodes (tree : AndTree state output inputs)
    (next : State v) (steps : List (Step v)) (checked : runSteps state steps = some next) :
    (tree.afterTrace next steps checked).nodes = tree.nodes := by
  induction tree <;> simp [AndTree.afterTrace, AndTree.nodes, *]

/-- Combine two already checked child traces with the actual binary parent
row. Each child aggregate is discharged once, including identity skips. -/
def projectTreeLongStep (left right output : Literal (Fin v))
    (leftInputs rightInputs : List (Literal (Fin v))) (leftNodes rightNodes : ℕ)
    (rows : BinaryAndRows state left right output)
    (first : AggregateProjection state left leftInputs (2 * leftNodes))
    (second : AggregateProjection first.state right rightInputs (2 * rightNodes)) :
    AggregateProjection state output (leftInputs ++ rightInputs) (2 * (leftNodes + rightNodes + 1)) := by
  have childrenChecked : runSteps state (first.steps ++ second.steps) = some second.state := by
    simp only [runSteps_append, first.checked, Option.bind_some]; exact second.checked
  let original := afterTrace (ofRow rows.longRow) second.state (first.steps ++ second.steps) childrenChecked
  let leftParent : AvailableSubclause second.state (negate left :: [output, negate right]) :=
    retarget original (by
      intro literal member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      aesop)
  let leftCertificate := first.result.afterTrace second.state second.steps second.checked
  let firstMerge := expandChild second.state left leftInputs [output, negate right] leftParent leftCertificate
  let rightParent : AvailableSubclause firstMerge.state
      (negate right :: (output :: leftInputs.map negate)) :=
    retarget firstMerge.result (by
      intro literal member
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      aesop)
  let rightCertificate := second.result.afterTrace firstMerge.state firstMerge.steps firstMerge.checked
  let secondMerge := expandChild firstMerge.state right rightInputs (output :: leftInputs.map negate) rightParent rightCertificate
  let finalRow : AvailableSubclause secondMerge.state (output :: (leftInputs ++ rightInputs).map negate) :=
    retarget secondMerge.result (by
      intro literal member
      simpa only [List.map_append, List.cons_append] using member)
  refine ⟨secondMerge.state,
    (first.steps ++ second.steps) ++ (firstMerge.steps ++ secondMerge.steps), ?_, .derived finalRow, ?_⟩
  · simp only [runSteps_append, childrenChecked, runSteps_append, firstMerge.checked, Option.bind_some]
    exact secondMerge.checked
  · have firstCount := first.count
    have secondCount := second.count
    have firstMergeCount := firstMerge.count
    have secondMergeCount := secondMerge.count
    simp only [List.length_append]
    omega

/-- Traverse a shared binary tree using exactly one recursive child result
per branch; proof search never runs inside this recursive computation. -/
def projectTreeLong {state : State v} {output : Literal (Fin v)}
    {inputs : List (Literal (Fin v))} (tree : AndTree state output inputs) :
    AggregateProjection state output inputs (2 * tree.nodes) := by
  match tree with
  | .leaf _ => exact ⟨state, [], rfl, .identity, by simp [AndTree.nodes]⟩
  | @AndTree.node _ _ left right leftInputs rightInputs leftTree rightTree output rows =>
    have leftPositive : 0 < leftInputs.length := by have := leftTree.nodes_leaves; omega
    have rightPositive : 0 < rightInputs.length := by have := rightTree.nodes_leaves; omega
    let first := projectTreeLong leftTree
    let rightCurrent := rightTree.afterTrace first.state first.steps first.checked
    let second := projectTreeLong (state := first.state) rightCurrent
    have secondTyped : AggregateProjection first.state right rightInputs (2 * rightTree.nodes) := by
      simpa only [rightCurrent, AndTree.afterTrace_nodes] using second
    exact projectTreeLongStep left right output leftInputs rightInputs leftTree.nodes rightTree.nodes rows first secondTyped
termination_by inputs.length
decreasing_by
  all_goals simp_all only [List.length_append]
  all_goals omega

/-- Assemble the three accepted tree traversals outside the recursive equations. -/
def appendTreeInputProjection (root left right : Literal (Fin v))
    (leftInputs rightInputs : List (Literal (Fin v))) (leftCount rightCount : ℕ)
    (localResult : InputProjection state root [left, right] 2)
    (first : InputProjection localResult.state root leftInputs (2 * leftCount))
    (second : InputProjection first.state root rightInputs (2 * rightCount)) :
    InputProjection state root (leftInputs ++ rightInputs) (2 * (leftCount + rightCount + 1)) := by
  refine ⟨second.state, localResult.steps ++ (first.steps ++ second.steps), ?_, ?_, ?_⟩
  · simp only [runSteps_append, localResult.checked, runSteps_append, first.checked, Option.bind_some]
    exact second.checked
  · intro input member
    if leftMem : input ∈ leftInputs then
      exact afterTrace (first.results input leftMem) second.state second.steps second.checked
    else
      have rightMem := (List.mem_append.mp member).resolve_left leftMem
      exact second.results input rightMem
  · have localCount := localResult.count
    have firstCount := first.count
    have secondCount := second.count
    simp only [List.length_append]
    omega


/-- Shared root-to-subtree implications are reused on both branches of the
balanced tree. Every internal node is processed once with at most two merges. -/
def projectTreeInputsBelow (tree : AndTree initial output inputs) (current : State v)
    (prefixSteps : List (Step v)) (checked : runSteps initial prefixSteps = some current)
    (root : Literal (Fin v)) (prefixRow : AvailableSubclause current [negate root, output]) :
    InputProjection current root inputs (2 * tree.nodes) := by
  match tree with
  | .leaf input =>
    refine ⟨current, [], rfl, ?_, by simp [AndTree.nodes]⟩
    intro leaf member
    have same : leaf = input := by simpa using member
    subst leaf; exact prefixRow
  | @AndTree.node _ _ left right leftInputs rightInputs leftTree rightTree output rows =>
    let localResult := descendCell initial current prefixSteps checked root left right output rows prefixRow
    have localChecked : runSteps initial (prefixSteps ++ localResult.steps) = some localResult.state := by
      simp only [runSteps_append, checked, Option.bind_some]; exact localResult.checked
    let leftPrefix := localResult.results left (by simp)
    let first := projectTreeInputsBelow leftTree localResult.state (prefixSteps ++ localResult.steps) localChecked root leftPrefix
    have firstChecked : runSteps initial ((prefixSteps ++ localResult.steps) ++ first.steps) = some first.state := by
      simp only [runSteps_append, localChecked, Option.bind_some]; exact first.checked
    let rightPrefix := afterTrace (localResult.results right (by simp)) first.state first.steps first.checked
    let second := projectTreeInputsBelow rightTree first.state ((prefixSteps ++ localResult.steps) ++ first.steps) firstChecked root rightPrefix
    exact appendTreeInputProjection root left right leftInputs rightInputs
      leftTree.nodes rightTree.nodes localResult first second

/-- Literal identity is an explicit no-row skip, not a supplied tautology axiom. -/
inductive DirectionalCertificate (state : State v) (root input : Literal (Fin v)) : Type
  | identity (same : root = input)
  | derived (row : AvailableSubclause state [negate root, input])

structure TreeInputProjection (initial : State v) (root : Literal (Fin v))
    (inputs : List (Literal (Fin v))) (budget : ℕ) where
  state : State v
  steps : List (Step v)
  checked : runSteps initial steps = some state
  results : ∀ input ∈ inputs, DirectionalCertificate state root input
  count : steps.length ≤ budget

/-- The top node begins with its two actual original implications. A source
unary fold is a leaf and emits only literal-identity skip certificates. -/
def projectTreeInputs (tree : AndTree state output inputs) :
    TreeInputProjection state output inputs (2 * tree.nodes) := by
  match tree with
  | .leaf input =>
    refine ⟨state, [], rfl, ?_, by simp [AndTree.nodes]⟩
    intro leaf member
    have same : leaf = input := by simpa using member
    exact .identity same.symm
  | @AndTree.node _ _ left right leftInputs rightInputs leftTree rightTree output rows =>
    let first := projectTreeInputsBelow leftTree state [] rfl output (ofRow rows.leftRow)
    let rightPrefix := afterTrace (ofRow rows.rightRow) first.state first.steps first.checked
    let second := projectTreeInputsBelow rightTree first.state first.steps first.checked output rightPrefix
    refine ⟨second.state, first.steps ++ second.steps, ?_, ?_, ?_⟩
    · simp only [runSteps_append, first.checked, Option.bind_some]; exact second.checked
    · intro input member
      if leftMem : input ∈ leftInputs then
        exact .derived (afterTrace (first.results input leftMem) second.state second.steps second.checked)
      else
        have rightMem := (List.mem_append.mp member).resolve_left leftMem
        exact .derived (second.results input rightMem)
    · have firstCount := first.count
      have secondCount := second.count
      simp only [List.length_append, AndTree.nodes]
      omega

 theorem projectTreeInputs_linear (tree : AndTree state output inputs) :
    (projectTreeInputs tree).steps.length ≤ 2 * (inputs.length - 1) := by
  have count := (projectTreeInputs tree).count
  have size := tree.nodes_leaves
  omega

 theorem projectTreeLong_linear (tree : AndTree state output inputs) :
    (projectTreeLong tree).steps.length ≤ 2 * (inputs.length - 1) := by
  have count := (projectTreeLong tree).count
  have size := tree.nodes_leaves
  omega

end Controller.NativeProof.FoldProjection
