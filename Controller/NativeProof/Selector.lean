module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Native.Encode
public import Controller.Resolution.Cases

@[expose] public section

/-! Structural selector proof components use actual earlier clause rows. A local
implication chain carries its propagation reason into the ordinary RUP producer;
no requested target is inserted among the original clauses. -/
namespace Controller.NativeProof.Selector
open Controller.CNF Controller.Resolution Controller.Resolution.RUP Controller.Resolution.Cases

variable {v : ℕ} {state : State v} {leftOut : Literal (Fin v)} {context : Clause (Fin v)}

/-- A concrete clause occurrence retains its actual checked-state identifier. -/
structure AvailableRow (state : State v) (clause : Clause (Fin v)) where
  id : ℕ
  present : state.rows id = some clause
  bound : id ≤ state.lastId

/-- Directional congruence composes two actual implication rows with one unit
propagation. This is the zero-split local selector component. -/
def chainTree (state : State v) (a b c : Literal (Fin v))
    (first : AvailableRow state [negate a, b])
    (second : AvailableRow state [negate b, c]) : CaseTree v :=
  .leaf ⟨second.id, [negate b, c],
    [⟨first.id, ⟨b, [negate a, b]⟩⟩]⟩

theorem chainTree_valid (state : State v) (a b c : Literal (Fin v))
    (first : AvailableRow state [negate a, b])
    (second : AvailableRow state [negate b, c]) :
    ValidTree state [negate a, c] (chainTree state a b c first second) := by
  refine ⟨second.present, second.bound, ?_, ?_, ?_⟩
  · intro reason member
    simp only [chainTree, List.mem_cons, List.not_mem_nil, or_false] at member
    subst reason
    exact ⟨first.present, first.bound, by simp⟩
  · constructor
    · constructor
      · simp
      · intro literal member different
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with same | same
        · subst literal; simp
        · exact False.elim (different same)
    · trivial
  · intro literal member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same <;> subst literal <;>
      simp [negations, chainTree]

@[simp] theorem chainTree_budget (state : State v) (a b c : Literal (Fin v))
    (first : AvailableRow state [negate a, b])
    (second : AvailableRow state [negate b, c]) :
    inferenceBudget (chainTree state a b c first second) = 1 := rfl

/-- Both directional implication rows, rather than semantic equality alone. -/
structure CongruenceRows (state : State v) (left right : Literal (Fin v)) where
  forward : AvailableRow state [negate left, right]
  backward : AvailableRow state [left, negate right]

/-- Selector schedules retain every bus/channel pair for each copy. -/
def localSchedule (channels buses : ℕ) : List (Bool × Fin buses × Fin channels) :=
  [false, true].flatMap fun side => (List.finRange buses).flatMap fun bus =>
    (List.finRange channels).map fun channel => (side, bus, channel)

@[simp] theorem localSchedule_count : (localSchedule channels buses).length = 2 * buses * channels := by
  simp [localSchedule, List.length_flatMap, Nat.mul_assoc]
  omega


/-- A retained input occurrence binds both directional propagation rows. -/
structure AndInput (state : State v) (leftOut : Literal (Fin v)) where
  left : Literal (Fin v)
  right : Literal (Fin v)
  leftRow : AvailableRow state [negate leftOut, left]
  transferRow : AvailableRow state [negate left, right]

def AndInput.reasons (input : AndInput state leftOut) : List (RowReason v) :=
  [⟨input.transferRow.id, ⟨input.right, [negate input.left, input.right]⟩⟩,
   ⟨input.leftRow.id, ⟨input.left, [negate leftOut, input.left]⟩⟩]

/-- Reverse order records right propagation after its left-input reason. -/
def andReasons (inputs : List (AndInput state leftOut)) : List (RowReason v) :=
  inputs.flatMap AndInput.reasons

@[simp] theorem andReasons_length (inputs : List (AndInput state leftOut)) :
    (andReasons inputs).length = 2 * inputs.length := by
  induction inputs with
  | nil => simp [andReasons]
  | cons input rest ih => simp [andReasons, AndInput.reasons, andReasons] at * <;> omega

theorem andReasons_known (inputs : List (AndInput state leftOut)) :
    KnownReasons state (andReasons inputs) := by
  intro reason member
  obtain ⟨input, inputMem, reasonMem⟩ := List.mem_flatMap.mp member
  simp only [AndInput.reasons, List.mem_cons, List.not_mem_nil, or_false] at reasonMem
  rcases reasonMem with same | same <;> subst reason
  · exact ⟨input.transferRow.present, input.transferRow.bound, by simp⟩
  · exact ⟨input.leftRow.present, input.leftRow.bound, by simp⟩

theorem andReasons_valid (inputs : List (AndInput state leftOut)) (rightOut : Literal (Fin v)) :
    ValidReasons [negate leftOut, rightOut] ((andReasons inputs).map RowReason.entry) := by
  induction inputs with
  | nil => trivial
  | cons input rest ih =>
    change ReasonEarlier input.right [negate input.left, input.right]
        (negate input.left :: negations ((andReasons rest).map RowReason.entry) ++ [negate leftOut, rightOut]) ∧
      ReasonEarlier input.left [negate leftOut, input.left]
        (negations ((andReasons rest).map RowReason.entry) ++ [negate leftOut, rightOut]) ∧ _
    refine ⟨⟨by simp, ?_⟩, ⟨by simp, ?_⟩, ih⟩
    · intro literal member different
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same
      · subst literal; simp
      · exact False.elim (different same)
    · intro literal member different
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same
      · subst literal; simp
      · exact False.elim (different same)

/-- The conflict row is the right AND's actual long clause. -/
def andTree (inputs : List (AndInput state leftOut)) (rightOut : Literal (Fin v))
    (rightRow : AvailableRow state (rightOut :: inputs.map fun input => negate input.right)) : CaseTree v :=
  .leaf ⟨rightRow.id, rightOut :: inputs.map (fun input => negate input.right), andReasons inputs⟩

theorem andTree_valid (inputs : List (AndInput state leftOut)) (rightOut : Literal (Fin v))
    (rightRow : AvailableRow state (rightOut :: inputs.map fun input => negate input.right)) :
    ValidTree state [negate leftOut, rightOut] (andTree inputs rightOut rightRow) := by
  refine ⟨rightRow.present, rightRow.bound, andReasons_known inputs, andReasons_valid inputs rightOut, ?_⟩
  intro literal member
  rcases List.mem_cons.mp member with same | inInputs
  · subst literal; simp
  · obtain ⟨input, inputMem, same⟩ := List.mem_map.mp inInputs
    subst literal
    apply List.mem_append.mpr
    left
    apply List.mem_map.mpr
    refine ⟨⟨input.right, [negate input.left, input.right]⟩, ?_, rfl⟩
    apply List.mem_map.mpr
    refine ⟨⟨input.transferRow.id, ⟨input.right, [negate input.left, input.right]⟩⟩, ?_, rfl⟩
    apply List.mem_flatMap.mpr
    exact ⟨input, inputMem, by simp [AndInput.reasons]⟩

@[simp] theorem andTree_budget (inputs : List (AndInput state leftOut)) (rightOut : Literal (Fin v))
    (rightRow : AvailableRow state (rightOut :: inputs.map fun input => negate input.right)) :
    inferenceBudget (andTree inputs rightOut rightRow) = 2 * inputs.length :=
  andReasons_length inputs

/-- Polarity-dual inputs use actual OR directional rows and earlier reverse
input congruences. The same zero-split structural producer handles arbitrary ORs. -/
structure OrInput (state : State v) (leftOut : Literal (Fin v)) where
  left : Literal (Fin v)
  right : Literal (Fin v)
  leftRow : AvailableRow state [leftOut, negate left]
  transferRow : AvailableRow state [left, negate right]

def OrInput.dual (input : OrInput state leftOut) : AndInput state (negate leftOut) where
  left := negate input.left
  right := negate input.right
  leftRow := by simpa using input.leftRow
  transferRow := by simpa using input.transferRow

def OrInput.aggregateRow (inputs : List (OrInput state leftOut)) (rightOut : Literal (Fin v))
    (rightRow : AvailableRow state (negate rightOut :: inputs.map OrInput.right)) :
    AvailableRow state (negate rightOut :: (inputs.map OrInput.dual).map fun input => negate input.right) := by
  simpa [OrInput.dual, Function.comp_def] using rightRow

def orTree (inputs : List (OrInput state leftOut)) (rightOut : Literal (Fin v))
    (rightRow : AvailableRow state (negate rightOut :: inputs.map OrInput.right)) : CaseTree v :=
  andTree (inputs.map OrInput.dual) (negate rightOut) (OrInput.aggregateRow inputs rightOut rightRow)

theorem orTree_valid (inputs : List (OrInput state leftOut)) (rightOut : Literal (Fin v))
    (rightRow : AvailableRow state (negate rightOut :: inputs.map OrInput.right)) :
    ValidTree state [leftOut, negate rightOut] (orTree inputs rightOut rightRow) := by
  change ValidTree state [leftOut, negate rightOut]
    (andTree (inputs.map OrInput.dual) (negate rightOut) (OrInput.aggregateRow inputs rightOut rightRow))
  simpa only [negate_negate] using andTree_valid (inputs.map OrInput.dual) (negate rightOut)
    (OrInput.aggregateRow inputs rightOut rightRow)

@[simp] theorem orTree_budget (inputs : List (OrInput state leftOut)) (rightOut : Literal (Fin v))
    (rightRow : AvailableRow state (negate rightOut :: inputs.map OrInput.right)) :
    inferenceBudget (orTree inputs rightOut rightRow) = 2 * inputs.length := by
  simp [orTree]

/-- Four ordered rows are precisely the native XOR gate definition. -/
structure XorRows (state : State v) (a b out : Literal (Fin v)) where
  zeroZero : AvailableRow state [a, b, negate out]
  oneOne : AvailableRow state [negate a, negate b, negate out]
  zeroOne : AvailableRow state [a, negate b, out]
  oneZero : AvailableRow state [negate a, b, out]

/-- Only the two left input variables are split. Even parity immediately
conflicts with the assumed left output; odd parity propagates the two right
inputs through existing congruence rows and conflicts at the right XOR row. -/
def xorTree (state : State v) (a b a' b' leftOut rightOut : Literal (Fin v))
    (left : XorRows state a b leftOut) (right : XorRows state a' b' rightOut)
    (first : CongruenceRows state a a') (second : CongruenceRows state b b') : CaseTree v :=
  .fork a
    (.fork b
      (.leaf ⟨left.oneOne.id, [negate a, negate b, negate leftOut], []⟩)
      (.leaf ⟨right.oneZero.id, [negate a', b', rightOut],
        [⟨second.backward.id, ⟨negate b', [b, negate b']⟩⟩,
         ⟨first.forward.id, ⟨a', [negate a, a']⟩⟩]⟩))
    (.fork b
      (.leaf ⟨right.zeroOne.id, [a', negate b', rightOut],
        [⟨second.forward.id, ⟨b', [negate b, b']⟩⟩,
         ⟨first.backward.id, ⟨negate a', [a, negate a']⟩⟩]⟩)
      (.leaf ⟨left.zeroZero.id, [a, b, negate leftOut], []⟩))

theorem xorTree_valid (state : State v) (a b a' b' leftOut rightOut : Literal (Fin v))
    (left : XorRows state a b leftOut) (right : XorRows state a' b' rightOut)
    (first : CongruenceRows state a a') (second : CongruenceRows state b b') :
    ValidTree state [negate leftOut, rightOut]
      (xorTree state a b a' b' leftOut rightOut left right first second) := by
  simp only [xorTree, ValidTree]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · refine ⟨left.oneOne.present, left.oneOne.bound, ?_, trivial, ?_⟩
    · simp [KnownReasons]
    · intro literal member
      simp only [List.mem_cons, List.not_mem_nil, List.mem_append, or_false, negations] at member ⊢
      aesop
  · refine ⟨right.oneZero.present, right.oneZero.bound, ?_, ?_, ?_⟩
    · intro reason member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same <;> subst reason
      · exact ⟨second.backward.present, second.backward.bound, by simp⟩
      · exact ⟨first.forward.present, first.forward.bound, by simp⟩
    · simp [ValidReasons, ReasonEarlier, negations] <;> aesop
    · intro literal member
      simp [ClauseSubset, negations] at *
      aesop
  · refine ⟨right.zeroOne.present, right.zeroOne.bound, ?_, ?_, ?_⟩
    · intro reason member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same <;> subst reason
      · exact ⟨second.forward.present, second.forward.bound, by simp⟩
      · exact ⟨first.backward.present, first.backward.bound, by simp⟩
    · simp [ValidReasons, ReasonEarlier, negations] <;> aesop
    · intro literal member
      simp [ClauseSubset, negations] at *
      aesop
  · refine ⟨left.zeroZero.present, left.zeroZero.bound, ?_, trivial, ?_⟩
    · simp [KnownReasons]
    · intro literal member
      simp only [List.mem_cons, List.not_mem_nil, List.mem_append, or_false, negations] at member ⊢
      aesop

@[simp] theorem xorTree_budget (state : State v) (a b a' b' leftOut rightOut : Literal (Fin v))
    (left : XorRows state a b leftOut) (right : XorRows state a' b' rightOut)
    (first : CongruenceRows state a a') (second : CongruenceRows state b b') :
    inferenceBudget (xorTree state a b a' b' leftOut rightOut left right first second) = 7 := rfl

theorem xorTree_depth (state : State v) (a b a' b' leftOut rightOut : Literal (Fin v))
    (left : XorRows state a b leftOut) (right : XorRows state a' b' rightOut)
    (first : CongruenceRows state a a') (second : CongruenceRows state b b') :
    DepthBound 2 (xorTree state a b a' b' leftOut rightOut left right first second) := by
  simp [xorTree, DepthBound]

/-- A retained input occurrence binds both directional propagation rows. -/
structure ContextAndInput (state : State v) (context : Clause (Fin v)) (leftOut : Literal (Fin v)) where
  left : Literal (Fin v)
  right : Literal (Fin v)
  leftRow : AvailableRow state [negate leftOut, left]
  transferRow : AvailableRow state (context ++ [negate left, right])

def ContextAndInput.reasons (input : ContextAndInput state context leftOut) : List (RowReason v) :=
  [⟨input.transferRow.id, ⟨input.right, context ++ [negate input.left, input.right]⟩⟩,
   ⟨input.leftRow.id, ⟨input.left, [negate leftOut, input.left]⟩⟩]

/-- Reverse order records right propagation after its left-input reason. -/
def contextAndReasons (inputs : List (ContextAndInput state context leftOut)) : List (RowReason v) :=
  inputs.flatMap ContextAndInput.reasons

@[simp] theorem contextAndReasons_length (inputs : List (ContextAndInput state context leftOut)) :
    (contextAndReasons inputs).length = 2 * inputs.length := by
  induction inputs with
  | nil => simp [contextAndReasons]
  | cons input rest ih => simp [contextAndReasons, ContextAndInput.reasons, contextAndReasons] at * <;> omega

theorem contextAndReasons_known (inputs : List (ContextAndInput state context leftOut)) :
    KnownReasons state (contextAndReasons inputs) := by
  intro reason member
  obtain ⟨input, inputMem, reasonMem⟩ := List.mem_flatMap.mp member
  simp only [ContextAndInput.reasons, List.mem_cons, List.not_mem_nil, or_false] at reasonMem
  rcases reasonMem with same | same <;> subst reason
  · exact ⟨input.transferRow.present, input.transferRow.bound, by simp⟩
  · exact ⟨input.leftRow.present, input.leftRow.bound, by simp⟩

theorem contextAndReasons_valid (inputs : List (ContextAndInput state context leftOut)) (rightOut : Literal (Fin v)) :
    ValidReasons (context ++ [negate leftOut, rightOut]) ((contextAndReasons inputs).map RowReason.entry) := by
  induction inputs with
  | nil => trivial
  | cons input rest ih =>
    change ReasonEarlier input.right (context ++ [negate input.left, input.right])
        (negate input.left :: negations ((contextAndReasons rest).map RowReason.entry) ++ (context ++ [negate leftOut, rightOut])) ∧
      ReasonEarlier input.left [negate leftOut, input.left]
        (negations ((contextAndReasons rest).map RowReason.entry) ++ (context ++ [negate leftOut, rightOut])) ∧ _
    refine ⟨⟨by simp, ?_⟩, ⟨by simp, ?_⟩, ih⟩
    · intro literal member different
      rcases List.mem_append.mp member with inContext | inPair
      · simp [inContext]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at inPair
        rcases inPair with same | same
        · subst literal; simp
        · exact False.elim (different same)
    · intro literal member different
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same
      · subst literal; simp
      · exact False.elim (different same)

/-- The conflict row is the right AND's actual long clause. -/
def contextAndTree (inputs : List (ContextAndInput state context leftOut)) (rightOut : Literal (Fin v))
    (rightRow : AvailableRow state (rightOut :: inputs.map fun input => negate input.right)) : CaseTree v :=
  .leaf ⟨rightRow.id, rightOut :: inputs.map (fun input => negate input.right), contextAndReasons inputs⟩

theorem contextAndTree_valid (inputs : List (ContextAndInput state context leftOut)) (rightOut : Literal (Fin v))
    (rightRow : AvailableRow state (rightOut :: inputs.map fun input => negate input.right)) :
    ValidTree state (context ++ [negate leftOut, rightOut]) (contextAndTree inputs rightOut rightRow) := by
  refine ⟨rightRow.present, rightRow.bound, contextAndReasons_known inputs, contextAndReasons_valid inputs rightOut, ?_⟩
  intro literal member
  rcases List.mem_cons.mp member with same | inInputs
  · subst literal; simp
  · obtain ⟨input, inputMem, same⟩ := List.mem_map.mp inInputs
    subst literal
    apply List.mem_append.mpr
    left
    apply List.mem_map.mpr
    refine ⟨⟨input.right, context ++ [negate input.left, input.right]⟩, ?_, rfl⟩
    apply List.mem_map.mpr
    refine ⟨⟨input.transferRow.id, ⟨input.right, context ++ [negate input.left, input.right]⟩⟩, ?_, rfl⟩
    apply List.mem_flatMap.mpr
    exact ⟨input, inputMem, by simp [ContextAndInput.reasons]⟩

@[simp] theorem contextAndTree_budget (inputs : List (ContextAndInput state context leftOut)) (rightOut : Literal (Fin v))
    (rightRow : AvailableRow state (rightOut :: inputs.map fun input => negate input.right)) :
    inferenceBudget (contextAndTree inputs rightOut rightRow) = 2 * inputs.length :=
  contextAndReasons_length inputs


/-- Contextual equalities are actual earlier rows retaining their cofactor guard. -/
structure ContextCongruenceRows (state : State v) (context : Clause (Fin v))
    (left right : Literal (Fin v)) where
  forward : AvailableRow state (context ++ [negate left, right])
  backward : AvailableRow state (context ++ [left, negate right])

/-- Polarity-dual inputs use actual OR directional rows and earlier reverse
input congruences. The same zero-split structural producer handles arbitrary ORs. -/
structure ContextOrInput (state : State v) (context : Clause (Fin v)) (leftOut : Literal (Fin v)) where
  left : Literal (Fin v)
  right : Literal (Fin v)
  leftRow : AvailableRow state [leftOut, negate left]
  transferRow : AvailableRow state (context ++ [left, negate right])

def ContextOrInput.dual (input : ContextOrInput state context leftOut) : ContextAndInput state context (negate leftOut) where
  left := negate input.left
  right := negate input.right
  leftRow := by simpa using input.leftRow
  transferRow := by simpa using input.transferRow

def ContextOrInput.aggregateRow (inputs : List (ContextOrInput state context leftOut)) (rightOut : Literal (Fin v))
    (rightRow : AvailableRow state (negate rightOut :: inputs.map ContextOrInput.right)) :
    AvailableRow state (negate rightOut :: (inputs.map ContextOrInput.dual).map fun input => negate input.right) := by
  simpa [ContextOrInput.dual, Function.comp_def] using rightRow

def contextOrTree (inputs : List (ContextOrInput state context leftOut)) (rightOut : Literal (Fin v))
    (rightRow : AvailableRow state (negate rightOut :: inputs.map ContextOrInput.right)) : CaseTree v :=
  contextAndTree (inputs.map ContextOrInput.dual) (negate rightOut) (ContextOrInput.aggregateRow inputs rightOut rightRow)

theorem contextOrTree_valid (inputs : List (ContextOrInput state context leftOut)) (rightOut : Literal (Fin v))
    (rightRow : AvailableRow state (negate rightOut :: inputs.map ContextOrInput.right)) :
    ValidTree state (context ++ [leftOut, negate rightOut]) (contextOrTree inputs rightOut rightRow) := by
  change ValidTree state (context ++ [leftOut, negate rightOut])
    (contextAndTree (inputs.map ContextOrInput.dual) (negate rightOut) (ContextOrInput.aggregateRow inputs rightOut rightRow))
  simpa only [negate_negate] using contextAndTree_valid (inputs.map ContextOrInput.dual) (negate rightOut)
    (ContextOrInput.aggregateRow inputs rightOut rightRow)

@[simp] theorem contextOrTree_budget (inputs : List (ContextOrInput state context leftOut)) (rightOut : Literal (Fin v))
    (rightRow : AvailableRow state (negate rightOut :: inputs.map ContextOrInput.right)) :
    inferenceBudget (contextOrTree inputs rightOut rightRow) = 2 * inputs.length := by
  simp [contextOrTree]

/-- Only the two left input variables are split. Even parity immediately
conflicts with the assumed left output; odd parity propagates the two right
inputs through existing congruence rows and conflicts at the right XOR row. -/
def contextXorTree (state : State v) (context : Clause (Fin v)) (a b a' b' leftOut rightOut : Literal (Fin v))
    (left : XorRows state a b leftOut) (right : XorRows state a' b' rightOut)
    (first : ContextCongruenceRows state context a a') (second : ContextCongruenceRows state context b b') : CaseTree v :=
  .fork a
    (.fork b
      (.leaf ⟨left.oneOne.id, [negate a, negate b, negate leftOut], []⟩)
      (.leaf ⟨right.oneZero.id, [negate a', b', rightOut],
        [⟨second.backward.id, ⟨negate b', (context ++ [b, negate b'])⟩⟩,
         ⟨first.forward.id, ⟨a', (context ++ [negate a, a'])⟩⟩]⟩))
    (.fork b
      (.leaf ⟨right.zeroOne.id, [a', negate b', rightOut],
        [⟨second.forward.id, ⟨b', (context ++ [negate b, b'])⟩⟩,
         ⟨first.backward.id, ⟨negate a', (context ++ [a, negate a'])⟩⟩]⟩)
      (.leaf ⟨left.zeroZero.id, [a, b, negate leftOut], []⟩))

theorem contextXorTree_valid (state : State v) (context : Clause (Fin v)) (a b a' b' leftOut rightOut : Literal (Fin v))
    (left : XorRows state a b leftOut) (right : XorRows state a' b' rightOut)
    (first : ContextCongruenceRows state context a a') (second : ContextCongruenceRows state context b b') :
    ValidTree state (context ++ [negate leftOut, rightOut])
      (contextXorTree state context a b a' b' leftOut rightOut left right first second) := by
  simp only [contextXorTree, ValidTree]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · refine ⟨left.oneOne.present, left.oneOne.bound, ?_, trivial, ?_⟩
    · simp [KnownReasons]
    · intro literal member
      simp only [List.mem_cons, List.not_mem_nil, List.mem_append, or_false, negations] at member ⊢
      aesop
  · refine ⟨right.oneZero.present, right.oneZero.bound, ?_, ?_, ?_⟩
    · intro reason member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same <;> subst reason
      · exact ⟨second.backward.present, second.backward.bound, by simp⟩
      · exact ⟨first.forward.present, first.forward.bound, by simp⟩
    · simp [ValidReasons, ReasonEarlier, negations] <;> aesop
    · intro literal member
      simp [ClauseSubset, negations] at *
      aesop
  · refine ⟨right.zeroOne.present, right.zeroOne.bound, ?_, ?_, ?_⟩
    · intro reason member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same <;> subst reason
      · exact ⟨second.forward.present, second.forward.bound, by simp⟩
      · exact ⟨first.backward.present, first.backward.bound, by simp⟩
    · simp [ValidReasons, ReasonEarlier, negations] <;> aesop
    · intro literal member
      simp [ClauseSubset, negations] at *
      aesop
  · refine ⟨left.zeroZero.present, left.zeroZero.bound, ?_, trivial, ?_⟩
    · simp [KnownReasons]
    · intro literal member
      simp only [List.mem_cons, List.not_mem_nil, List.mem_append, or_false, negations] at member ⊢
      aesop

@[simp] theorem contextXorTree_budget (state : State v) (context : Clause (Fin v)) (a b a' b' leftOut rightOut : Literal (Fin v))
    (left : XorRows state a b leftOut) (right : XorRows state a' b' rightOut)
    (first : ContextCongruenceRows state context a a') (second : ContextCongruenceRows state context b b') :
    inferenceBudget (contextXorTree state context a b a' b' leftOut rightOut left right first second) = 7 := rfl

theorem contextXorTree_depth (state : State v) (context : Clause (Fin v)) (a b a' b' leftOut rightOut : Literal (Fin v))
    (left : XorRows state a b leftOut) (right : XorRows state a' b' rightOut)
    (first : ContextCongruenceRows state context a a') (second : ContextCongruenceRows state context b b') :
    DepthBound 2 (contextXorTree state context a b a' b' leftOut rightOut left right first second) := by
  simp [contextXorTree, DepthBound]


end Controller.NativeProof.Selector
