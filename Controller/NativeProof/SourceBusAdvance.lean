module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceBusSchedule
public import Controller.NativeProof.SourceStageXor

@[expose] public section

/-! Concrete bus advancement joins actual allocator outputs and checked prior
subclauses. Slot identities follow the represented source traversal. -/
namespace Controller.NativeProof.SourceBusAdvance
open Controller.Native Controller.Native.SourceController Controller.CNF
open Controller.Resolution Controller.Resolution.Cases
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceFoldOccurrences Controller.NativeProof.SourceFoldOwners
open Controller.NativeProof.SourceCongruence Controller.NativeProof.SourceSlotFrames
open Controller.NativeProof.SourceRoleFrames Controller.NativeProof.SourceStageCongruence
open Controller.NativeProof.SourceStagePolarity Controller.NativeProof.SourceStageXor
open Controller.NativeProof.SourceBusSchedule
variable {parameters : Parameters} {v : Nat}

/-- A term allocator assigns its output once, and all remaining term channels
retain that same physical handle. -/
theorem busTerms_term_output (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    (busTerms side (laterBuses (parameters := parameters))[position.val] (busBefore side position)).slots
      (.internal (.term side (laterBuses (parameters := parameters))[position.val] channel)) =
      (SourceSerialFold.allocate .conjunction (termBefore side position channel).lastID
        (laterTermInputs side position channel)).output := by
  let values := List.finRange parameters.channels
  let bus := (laterBuses (parameters := parameters))[position.val]
  have bound : channel.val < values.length := by simpa [values] using channel.isLt
  have split := positional_decomposition values ⟨channel.val, bound⟩
  have decomposition : values = values.take channel.val ++ channel :: values.drop (channel.val + 1) := by
    simpa [values] using split
  have unique : (values.take channel.val ++ channel :: values.drop (channel.val + 1)).Nodup := by
    rw [← decomposition]
    exact List.nodup_finRange parameters.channels
  have absent : channel ∉ values.drop (channel.val + 1) :=
    (List.nodup_cons.mp (List.nodup_append.mp unique).2.1).1
  change (values.foldl (termStep side bus) (busBefore side position)).slots _ = _
  rw [decomposition, List.foldl_append, List.foldl_cons]
  rw [foldl_slot_mem _ (.internal (.term side bus channel)) _ (by
    intro current index member
    apply foldNative_other
    have different : index ≠ channel := by
      intro same
      exact absent (same ▸ member)
    simp [different, Ne.symm different])]
  simp [termStep, termBefore, occurrenceCursor, laterTermInputs,
    Cursor.foldNative, Cursor.assign, values, bus]

theorem laterFlagInputs_eq_terms (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) :
    (laterFlagInputs side position).map (mapLiteral rename) =
      (List.finRange parameters.channels).map (laterTermOutput rename side position) := by
  unfold laterFlagInputs
  rw [List.map_map]
  apply List.map_congr_left
  intro channel member
  change mapLiteral rename ((busTerms side _ (busBefore side position)).slots _) = _
  rw [busTerms_term_output]
  rfl

theorem busMaskStep_term_frame (side querySide : Side) (bus queryBus : Fin parameters.buses)
    (index channel : Fin parameters.channels) (cursor : Cursor parameters) :
    (busMaskStep side bus cursor index).slots (.internal (.term querySide queryBus channel)) =
      cursor.slots (.internal (.term querySide queryBus channel)) := by
  simp [busMaskStep, Cursor.emitNative, Cursor.emit, Cursor.assign]

theorem laterAbsentInput_eq_termOutput (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    laterAbsentInput rename side position channel = laterTermOutput rename side position channel := by
  unfold laterAbsentInput laterAbsentBefore occurrenceCursor
  rw [foldl_slot _ _ (fun current index => busMaskStep_term_frame side side _ _ index channel current)]
  unfold busFlag
  rw [foldNative_other _ _ _ _ _ (by simp)]
  rw [busTerms_term_output]
  rfl

theorem busMaskStep_flag_frame (side querySide : Side) (bus queryBus : Fin parameters.buses)
    (index : Fin parameters.channels) (cursor : Cursor parameters) :
    (busMaskStep side bus cursor index).slots (.internal (.flag querySide queryBus)) =
      cursor.slots (.internal (.flag querySide queryBus)) := by
  simp [busMaskStep, Cursor.emitNative, Cursor.emit, Cursor.assign]

theorem laterMaskFlag_eq_flagOutput (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    laterMaskFlag rename side position channel = laterFlagOutput rename side position := by
  unfold laterMaskFlag laterMaskBefore
  rw [emitNative_other _ _ _ _ (by simp)]
  unfold laterAbsentBefore occurrenceCursor
  rw [foldl_slot _ _ (fun current index => busMaskStep_flag_frame side side _ _ index current)]
  simp [busFlag, Cursor.foldNative, Cursor.assign, laterFlagOutput, laterFlagInputs]

theorem laterMaskAbsent_eq_absentOutput (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    laterMaskAbsent rename side position channel = laterAbsentOutput rename side position channel := by
  simp [laterMaskAbsent, laterMaskBefore, laterAbsentOutput, Cursor.emitNative, Cursor.emit, Cursor.assign]

structure PairedProjection (start : State v) (context : Clause (Fin v))
    (left right : Literal (Fin v)) (budget : Nat) where
  state : State v
  steps : List (Step v)
  checked : runSteps start steps = some state
  pair : DirectionPair state context left right
  count : steps.length ≤ budget

def pairedAnd (state : State v) (context : Clause (Fin v))
    (leftOut rightOut : Literal (Fin v)) (pairs : List (Literal (Fin v) × Literal (Fin v)))
    (nonempty : pairs ≠ [])
    (leftTree : AndTree state leftOut (pairs.map Prod.fst))
    (rightTree : AndTree state rightOut (pairs.map Prod.snd))
    (transfers : ∀ pair ∈ pairs, DirectionPair state context pair.1 pair.2) :
    PairedProjection state context leftOut rightOut (12 * pairs.length) := by
  let first := guardedAndPositive state context leftOut rightOut pairs nonempty leftTree rightTree
    (fun pair member => (transfers pair member).forward)
  let reversed := pairs.map Prod.swap
  have reversedNonempty : reversed ≠ [] := by
    intro empty
    exact nonempty (List.map_eq_nil_iff.mp empty)
  let nextLeft : AndTree first.state rightOut (reversed.map Prod.fst) := by
    simpa only [reversed, List.map_map, Function.comp_def, Prod.fst_swap] using
      rightTree.afterTrace first.state first.steps first.checked
  let nextRight : AndTree first.state leftOut (reversed.map Prod.snd) := by
    simpa only [reversed, List.map_map, Function.comp_def, Prod.snd_swap] using
      leftTree.afterTrace first.state first.steps first.checked
  let nextTransfers := fun pair (member : pair ∈ reversed) =>
    let selected := mappedChoice Prod.swap pair pairs member
    let old := (transfers selected.val selected.property.1).backward
    (show GuardedTransfer first.state context pair.1 pair.2 from by
      have same := selected.property.2
      simpa only [← same, Prod.fst_swap, Prod.snd_swap] using old.afterTrace first.state first.steps first.checked)
  let second := guardedAndPositive first.state context rightOut leftOut reversed reversedNonempty nextLeft nextRight nextTransfers
  refine ⟨second.state, first.steps ++ second.steps, ?_,
    ⟨first.result.afterTrace second.state second.steps second.checked, second.result⟩, ?_⟩
  · rw [runSteps_append, first.checked]
    exact second.checked
  · have one := first.count
    have two := second.count
    simp only [List.length_append]
    simp only [reversed, List.length_map] at two
    omega

/-- The bidirectional term stage binds both allocator trees at the source
occurrence and constructs each input certificate from the completed table. -/
def laterTermPairFromTable (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (table : BusMaskTable (parameters := parameters) rename flag position.val) :
    PairedProjection table.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
      (laterTermOutput rename .healthy position channel) (laterTermOutput rename .faulty position channel)
      (12 * (laterTermPairs rename position channel).length) := by
  let pairs := laterTermPairs rename position channel
  let left : AndTree table.checkedPrefix.state (laterTermOutput rename .healthy position channel) (pairs.map Prod.fst) := by
    dsimp only [pairs]
    rw [laterTermPairs_fst]
    exact (laterTermTree rename .healthy position channel).afterTrace table.checkedPrefix.state table.checkedPrefix.steps table.checkedPrefix.checked
  let right : AndTree table.checkedPrefix.state (laterTermOutput rename .faulty position channel) (pairs.map Prod.snd) := by
    dsimp only [pairs]
    rw [laterTermPairs_snd]
    exact (laterTermTree rename .faulty position channel).afterTrace table.checkedPrefix.state table.checkedPrefix.steps table.checkedPrefix.checked
  exact pairedAnd table.checkedPrefix.state _ _ _ pairs (by
    have bound := laterTermPairs_two rename position channel
    intro empty
    simp only [pairs, empty, List.length_nil] at bound
    omega) left right (fun pair member => termPairDirection rename flag position channel table pair member)

structure TermBank (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (start : SourcePrefix (parameters := parameters) rename) (done : List (Fin parameters.channels)) where
  state : State v
  steps : List (Step v)
  checked : runSteps start.state steps = some state
  pairs : ∀ channel ∈ done, DirectionPair state (equalFlagContext (parameters := parameters) rename flag)
    (laterTermOutput rename .healthy position channel) (laterTermOutput rename .faulty position channel)
  count : steps.length ≤ done.length * (12 * (2 + ((List.finRange parameters.buses).filter
    (fun earlier => earlier < (laterBuses (parameters := parameters))[position.val])).length))

theorem laterTermPairs_length (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    (laterTermPairs rename position channel).length =
      2 + ((List.finRange parameters.buses).filter (fun earlier => earlier < (laterBuses (parameters := parameters))[position.val])).length := by
  have length := congrArg List.length (laterTermPairs_fst rename position channel)
  simpa only [List.length_map, laterTermInputs, List.length_append, List.length_cons, List.length_nil] using length

def BusMaskTable.afterTrace (table : BusMaskTable (parameters := parameters) rename flag count)
    (next : State v) (steps : List (Step v)) (checked : runSteps table.checkedPrefix.state steps = some next) :
    BusMaskTable (parameters := parameters) rename flag count where
  checkedPrefix := table.checkedPrefix.extend next steps checked
  directions := fun bus member channel => (table.directions bus member channel).afterTrace next steps checked

def termBankStep (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : BusMaskTable (parameters := parameters) rename flag position.val)
    (done : List (Fin parameters.channels)) (bank : TermBank rename flag position table.checkedPrefix done)
    (channel : Fin parameters.channels) : TermBank rename flag position table.checkedPrefix (channel :: done) := by
  let extended := BusMaskTable.afterTrace table bank.state bank.steps bank.checked
  let added := laterTermPairFromTable rename flag position channel extended
  refine ⟨added.state, bank.steps ++ added.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, bank.checked]
    exact added.checked
  · intro query member
    by_cases same : query = channel
    · subst query
      exact added.pair
    · have old : query ∈ done := (List.mem_cons.mp member).resolve_left same
      exact (bank.pairs query old).afterTrace added.state added.steps added.checked
  · have one := bank.count
    have two : added.steps.length ≤ 12 *
        (2 + ((List.finRange parameters.buses).filter
          (fun earlier => earlier < (laterBuses (parameters := parameters))[position.val])).length) := by
      calc
        added.steps.length ≤ 12 * (laterTermPairs rename position channel).length := added.count
        _ = _ := congrArg (fun size => 12 * size) (laterTermPairs_length rename position channel)
    simp only [List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

def buildTermBank (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : BusMaskTable (parameters := parameters) rename flag position.val) :
    (channels : List (Fin parameters.channels)) → TermBank rename flag position table.checkedPrefix channels
  | [] => ⟨table.checkedPrefix.state, [], rfl, (by intro channel member; exact False.elim (List.not_mem_nil member)), (by simp)⟩
  | channel :: channels => termBankStep rename flag position table channels (buildTermBank rename flag position table channels) channel

def pairedOr (state : State v) (context : Clause (Fin v))
    (leftOut rightOut : Literal (Fin v)) (pairs : List (Literal (Fin v) × Literal (Fin v)))
    (nonempty : pairs ≠ [])
    (leftTree : AndTree state (negate leftOut) ((pairs.map Prod.fst).map negate))
    (rightTree : AndTree state (negate rightOut) ((pairs.map Prod.snd).map negate))
    (transfers : ∀ pair ∈ pairs, DirectionPair state context pair.1 pair.2) :
    PairedProjection state context leftOut rightOut (12 * pairs.length) := by
  let first := guardedOr state context leftOut rightOut pairs nonempty leftTree rightTree
    (fun pair member => (transfers pair member).forward)
  let reversed := pairs.map Prod.swap
  have reversedNonempty : reversed ≠ [] := by
    intro empty
    exact nonempty (List.map_eq_nil_iff.mp empty)
  let nextLeft : AndTree first.state (negate rightOut) ((reversed.map Prod.fst).map negate) := by
    simpa only [reversed, List.map_map, Function.comp_def, Prod.fst_swap] using
      rightTree.afterTrace first.state first.steps first.checked
  let nextRight : AndTree first.state (negate leftOut) ((reversed.map Prod.snd).map negate) := by
    simpa only [reversed, List.map_map, Function.comp_def, Prod.snd_swap] using
      leftTree.afterTrace first.state first.steps first.checked
  let nextTransfers := fun pair (member : pair ∈ reversed) =>
    let selected := mappedChoice Prod.swap pair pairs member
    let old := (transfers selected.val selected.property.1).backward
    (show GuardedTransfer first.state context pair.1 pair.2 from by
      have same := selected.property.2
      simpa only [← same, Prod.fst_swap, Prod.snd_swap] using old.afterTrace first.state first.steps first.checked)
  let second := guardedOr first.state context rightOut leftOut reversed reversedNonempty nextLeft nextRight nextTransfers
  refine ⟨second.state, first.steps ++ second.steps, ?_,
    ⟨first.result.afterTrace second.state second.steps second.checked, second.result⟩, ?_⟩
  · rw [runSteps_append, first.checked]
    exact second.checked
  · have one := first.count
    have two := second.count
    simp only [List.length_append]
    simp only [reversed, List.length_map] at two
    omega

def TermBank.checkedPrefix (bank : TermBank (parameters := parameters) rename flag position start done) :
    SourcePrefix (parameters := parameters) rename := start.extend bank.state bank.steps bank.checked

theorem laterFlagPairs_eq_terms (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length) :
    laterFlagPairs rename position = (List.finRange parameters.channels).map fun channel =>
      (laterTermOutput rename .healthy position channel, laterTermOutput rename .faulty position channel) := by
  unfold laterFlagPairs
  rw [laterFlagInputs_eq_terms, laterFlagInputs_eq_terms]
  exact List.zip_map'

def flagPairDirection (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (start : SourcePrefix (parameters := parameters) rename)
    (bank : TermBank rename flag position start (List.finRange parameters.channels))
    (pair : Literal (Fin v) × Literal (Fin v)) (member : pair ∈ laterFlagPairs rename position) :
    DirectionPair bank.state (equalFlagContext (parameters := parameters) rename flag) pair.1 pair.2 := by
  have represented : pair ∈ (List.finRange parameters.channels).map (fun channel =>
      (laterTermOutput rename .healthy position channel, laterTermOutput rename .faulty position channel)) := by
    simpa only [← laterFlagPairs_eq_terms rename position] using member
  let selected := mappedChoice (fun channel =>
    (laterTermOutput rename .healthy position channel, laterTermOutput rename .faulty position channel))
    pair (List.finRange parameters.channels) represented
  have certificate := bank.pairs selected.val selected.property.1
  have same := selected.property.2
  simpa only [← same] using certificate

/-- Both OR directions use the actual balanced flag-fold producer rows and
construct their child certificates from the completed term bank. -/
def laterFlagPairFromTerms (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (start : SourcePrefix (parameters := parameters) rename)
    (bank : TermBank rename flag position start (List.finRange parameters.channels)) :
    PairedProjection bank.state (equalFlagContext (parameters := parameters) rename flag)
      (laterFlagOutput rename .healthy position) (laterFlagOutput rename .faulty position)
      (12 * (laterFlagPairs rename position).length) := by
  let checkedPrefix := bank.checkedPrefix
  let left : AndTree bank.state (negate (laterFlagOutput rename .healthy position))
      (((laterFlagPairs rename position).map Prod.fst).map negate) := by
    rw [laterFlagPairs_fst]
    have actual : AndTree bank.state (negate (laterFlagOutput rename .healthy position))
        ((laterFlagInputs .healthy position).map (fun literal => negate (mapLiteral rename literal))) :=
      (laterFlagTree rename .healthy position).afterTrace bank.state checkedPrefix.steps checkedPrefix.checked
    simpa only [List.map_map, Function.comp_def] using actual
  let right : AndTree bank.state (negate (laterFlagOutput rename .faulty position))
      (((laterFlagPairs rename position).map Prod.snd).map negate) := by
    rw [laterFlagPairs_snd]
    have actual : AndTree bank.state (negate (laterFlagOutput rename .faulty position))
        ((laterFlagInputs .faulty position).map (fun literal => negate (mapLiteral rename literal))) :=
      (laterFlagTree rename .faulty position).afterTrace bank.state checkedPrefix.steps checkedPrefix.checked
    simpa only [List.map_map, Function.comp_def] using actual
  exact pairedOr bank.state _ _ _ _ (laterFlagPairs_nonempty rename position) left right
    (fun pair member => flagPairDirection rename flag position start bank pair member)

/-- The two NOT directions consume opposite term directions at the exact
absent emission inputs. No NOT row is supplied by the caller. -/
def laterAbsentPairFromTerm (rename : Nat → Fin v) (context : Clause (Fin v))
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (start : SourcePrefix (parameters := parameters) rename)
    (terms : DirectionPair start.state context (laterTermOutput rename .healthy position channel)
      (laterTermOutput rename .faulty position channel)) :
    PairedProjection start.state context (laterAbsentOutput rename .healthy position channel)
      (laterAbsentOutput rename .faulty position channel) 4 := by
  let inputs : DirectionPair start.state context (laterAbsentInput rename .healthy position channel)
      (laterAbsentInput rename .faulty position channel) := by
    simpa only [laterAbsentInput_eq_termOutput] using terms
  let left := laterAbsentNativeRows rename .healthy position channel start
  let right := laterAbsentNativeRows rename .faulty position channel start
  let first := guardedNot start.state context _ _ _ _ left right inputs.backward
  let nextLeft := left.afterTrace first.state first.steps first.checked
  let nextRight := right.afterTrace first.state first.steps first.checked
  let second := guardedNot first.state context _ _ _ _ nextRight nextLeft
    (inputs.forward.afterTrace first.state first.steps first.checked)
  refine ⟨second.state, first.steps ++ second.steps, ?_,
    ⟨.derived (FoldProjection.afterTrace first.result second.state second.steps second.checked), .derived second.result⟩, ?_⟩
  · rw [runSteps_append, first.checked]
    exact second.checked
  · have one := first.count
    have two := second.count
    simp only [List.length_append]
    omega

/-- Original XOR occurrences consume the constructed flag and absent banks.
The reverse direction swaps copies and transports all earlier rows. -/
def laterMaskPairFromStages (rename : Nat → Fin v) (context : Clause (Fin v))
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (start : SourcePrefix (parameters := parameters) rename)
    (flags : DirectionPair start.state context (laterFlagOutput rename .healthy position)
      (laterFlagOutput rename .faulty position))
    (absent : DirectionPair start.state context (laterAbsentOutput rename .healthy position channel)
      (laterAbsentOutput rename .faulty position channel)) :
    PairedProjection start.state context (laterMaskOutput rename .healthy position channel)
      (laterMaskOutput rename .faulty position channel) 22 := by
  let flagInputs : DirectionPair start.state context (laterMaskFlag rename .healthy position channel)
      (laterMaskFlag rename .faulty position channel) := by
    simpa only [laterMaskFlag_eq_flagOutput] using flags
  let absentInputs : DirectionPair start.state context (laterMaskAbsent rename .healthy position channel)
      (laterMaskAbsent rename .faulty position channel) := by
    simpa only [laterMaskAbsent_eq_absentOutput] using absent
  let left := laterMaskNativeRows rename .healthy position channel start
  let right := laterMaskNativeRows rename .faulty position channel start
  let first := guardedXor start.state context _ _ _ _ _ _ left right
    flagInputs.forward flagInputs.backward absentInputs.forward absentInputs.backward
  let nextFlags := flagInputs.afterTrace first.state first.steps first.checked
  let nextAbsent := absentInputs.afterTrace first.state first.steps first.checked
  let second := guardedXor first.state context _ _ _ _ _ _
    (right.afterTrace first.state first.steps first.checked) (left.afterTrace first.state first.steps first.checked)
    nextFlags.backward nextFlags.forward nextAbsent.backward nextAbsent.forward
  refine ⟨second.state, first.steps ++ second.steps, ?_,
    ⟨.derived (FoldProjection.afterTrace first.result second.state second.steps second.checked), .derived second.result⟩, ?_⟩
  · rw [runSteps_append, first.checked]
    exact second.checked
  · have one := first.count
    have two := second.count
    simp only [List.length_append]
    omega

/-- Each channel's absent/mask substage performs at most 26 actual inferences,
including both output directions and all cofactor merges. -/
def laterMaskChannelFromBanks (rename : Nat → Fin v) (context : Clause (Fin v))
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (start : SourcePrefix (parameters := parameters) rename)
    (terms : DirectionPair start.state context (laterTermOutput rename .healthy position channel)
      (laterTermOutput rename .faulty position channel))
    (flags : DirectionPair start.state context (laterFlagOutput rename .healthy position)
      (laterFlagOutput rename .faulty position)) :
    PairedProjection start.state context (laterMaskOutput rename .healthy position channel)
      (laterMaskOutput rename .faulty position channel) 26 := by
  let first := laterAbsentPairFromTerm rename context position channel start terms
  let nextPrefix := start.extend first.state first.steps first.checked
  let second := laterMaskPairFromStages rename context position channel nextPrefix
    (flags.afterTrace first.state first.steps first.checked) first.pair
  refine ⟨second.state, first.steps ++ second.steps, ?_, second.pair, ?_⟩
  · rw [runSteps_append, first.checked]
    exact second.checked
  · have one := first.count
    have two := second.count
    simp only [List.length_append]
    omega

structure MaskInputs (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length) where
  checkedPrefix : SourcePrefix (parameters := parameters) rename
  terms : ∀ channel : Fin parameters.channels,
    DirectionPair checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
      (laterTermOutput rename .healthy position channel) (laterTermOutput rename .faulty position channel)
  flags : DirectionPair checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
    (laterFlagOutput rename .healthy position) (laterFlagOutput rename .faulty position)

def MaskInputs.afterTrace (inputs : MaskInputs (parameters := parameters) rename flag position)
    (next : State v) (steps : List (Step v)) (checked : runSteps inputs.checkedPrefix.state steps = some next) :
    MaskInputs (parameters := parameters) rename flag position where
  checkedPrefix := inputs.checkedPrefix.extend next steps checked
  terms := fun channel => (inputs.terms channel).afterTrace next steps checked
  flags := inputs.flags.afterTrace next steps checked

structure MaskBank (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (inputs : MaskInputs (parameters := parameters) rename flag position) (done : List (Fin parameters.channels)) where
  state : State v
  steps : List (Step v)
  checked : runSteps inputs.checkedPrefix.state steps = some state
  pairs : ∀ channel ∈ done, DirectionPair state (equalFlagContext (parameters := parameters) rename flag)
    (laterMaskOutput rename .healthy position channel) (laterMaskOutput rename .faulty position channel)
  count : steps.length ≤ 26 * done.length

def maskBankStep (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (inputs : MaskInputs (parameters := parameters) rename flag position)
    (done : List (Fin parameters.channels)) (bank : MaskBank rename flag position inputs done)
    (channel : Fin parameters.channels) : MaskBank rename flag position inputs (channel :: done) := by
  let extended := inputs.afterTrace bank.state bank.steps bank.checked
  let added := laterMaskChannelFromBanks rename (equalFlagContext (parameters := parameters) rename flag)
    position channel extended.checkedPrefix (extended.terms channel) extended.flags
  refine ⟨added.state, bank.steps ++ added.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, bank.checked]
    exact added.checked
  · intro query member
    by_cases same : query = channel
    · subst query
      exact added.pair
    · have old : query ∈ done := (List.mem_cons.mp member).resolve_left same
      exact (bank.pairs query old).afterTrace added.state added.steps added.checked
  · have one := bank.count
    have two := added.count
    simp only [List.length_append, List.length_cons]
    omega

def buildMaskBank (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (inputs : MaskInputs (parameters := parameters) rename flag position) :
    (channels : List (Fin parameters.channels)) → MaskBank rename flag position inputs channels
  | [] => ⟨inputs.checkedPrefix.state, [], rfl, (by intro channel member; exact False.elim (List.not_mem_nil member)), (by simp)⟩
  | channel :: channels => maskBankStep rename flag position inputs channels (buildMaskBank rename flag position inputs channels) channel

structure CurrentBusProjection (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : BusMaskTable (parameters := parameters) rename flag position.val) where
  state : State v
  steps : List (Step v)
  checked : runSteps table.checkedPrefix.state steps = some state
  pairs : ∀ channel : Fin parameters.channels,
    DirectionPair state (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename ((stagesBefore (parameters := parameters) .healthy (position.val + 1)).slots
        (.internal (.mask .healthy (laterBuses (parameters := parameters))[position.val] channel))))
      (mapLiteral rename ((stagesBefore (parameters := parameters) .faulty (position.val + 1)).slots
        (.internal (.mask .faulty (laterBuses (parameters := parameters))[position.val] channel))))
  count : steps.length ≤ 12 * parameters.channels *
    (2 + ((List.finRange parameters.buses).filter (fun earlier => earlier < (laterBuses (parameters := parameters))[position.val])).length) +
    38 * parameters.channels

/-- The actual term, flag, absent and mask traces are concatenated. Every
new mask certificate names the physical handle at the next source boundary. -/
def currentBusFromTable (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : BusMaskTable (parameters := parameters) rename flag position.val) : CurrentBusProjection rename flag position table := by
  let terms := buildTermBank rename flag position table (List.finRange parameters.channels)
  let flags := laterFlagPairFromTerms rename flag position table.checkedPrefix terms
  let inputs : MaskInputs (parameters := parameters) rename flag position :=
    ⟨terms.checkedPrefix.extend flags.state flags.steps flags.checked,
      fun channel => (terms.pairs channel (by simp)).afterTrace flags.state flags.steps flags.checked, flags.pair⟩
  let masks := buildMaskBank rename flag position inputs (List.finRange parameters.channels)
  refine ⟨masks.state, (terms.steps ++ flags.steps) ++ masks.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, runSteps_append, terms.checked]
    simp only [Option.bind_some, flags.checked]
    exact masks.checked
  · intro channel
    have certificate := masks.pairs channel (by simp)
    simpa only [stagesBefore_current_mask, laterMaskOutput] using certificate
  · have one := terms.count
    have three := masks.count
    have length : (laterFlagPairs rename position).length = parameters.channels := by
      rw [laterFlagPairs_eq_terms, List.length_map, List.length_finRange]
    have two : flags.steps.length ≤ 12 * parameters.channels := by
      calc
        flags.steps.length ≤ 12 * (laterFlagPairs rename position).length := flags.count
        _ = _ := congrArg (fun size => 12 * size) length
    simp only [List.length_finRange] at one three
    have normalized : terms.steps.length ≤ 12 * parameters.channels *
        (2 + ((List.finRange parameters.buses).filter
          (fun earlier => earlier < (laterBuses (parameters := parameters))[position.val])).length) := by
      simpa only [Nat.mul_assoc, Nat.mul_left_comm] using one
    simp only [List.length_append]
    omega

/-- Old masks retain their physical handles across the actual new bus, and
all current masks come from the newly checked channel bank. -/
def busTableAdvance (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : BusMaskTable (parameters := parameters) rename flag position.val) :
    BusMaskTable (parameters := parameters) rename flag (position.val + 1) := by
  let added := currentBusFromTable rename flag position table
  let nextPrefix := table.checkedPrefix.extend added.state added.steps added.checked
  refine ⟨nextPrefix, ?_⟩
  intro query member channel
  by_cases same : query = (laterBuses (parameters := parameters))[position.val]
  · subst query
    exact added.pairs channel
  · have oldMem : query ∈ parameters.firstBus :: (laterBuses (parameters := parameters)).take position.val := by
      rw [List.take_succ_eq_append_getElem position.isLt] at member
      simp only [List.mem_cons, List.mem_append, List.mem_singleton] at member ⊢
      aesop
    have certificate := (table.directions query oldMem channel).afterTrace added.state added.steps added.checked
    rw [stagesBefore_succ, stagesBefore_succ,
      laterBus_mask_other .healthy .healthy _ query channel same,
      laterBus_mask_other .faulty .faulty _ query channel same]
    exact certificate

/-- Primitive source-prefix recursion constructs every mask table from the
original first-mask seed. Bounds supply only finite list indices. -/
def buildBusPrefix (rename : Nat → Fin v) (flag : Bool) :
    (count : Nat) → count ≤ (laterBuses (parameters := parameters)).length →
      BusMaskTable (parameters := parameters) rename flag count
  | 0, _ => busMaskTableInitial rename flag
  | count + 1, bound =>
      let position : Fin (laterBuses (parameters := parameters)).length := ⟨count, by omega⟩
      busTableAdvance rename flag position (buildBusPrefix rename flag count (by omega))

def allBusMasks (rename : Nat → Fin v) (flag : Bool) :
    BusMaskTable (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length :=
  buildBusPrefix rename flag _ (Nat.le_refl _)

def stageBudget (bus : Fin parameters.buses) : Nat :=
  12 * parameters.channels * (2 + ((List.finRange parameters.buses).filter (fun earlier => earlier < bus)).length) +
    38 * parameters.channels

def prefixBudget (count : Nat) : Nat :=
  2 * parameters.channels + (((laterBuses (parameters := parameters)).take count).map (stageBudget (parameters := parameters))).sum

theorem prefixBudget_succ (position : Fin (laterBuses (parameters := parameters)).length) :
    prefixBudget (parameters := parameters) (position.val + 1) =
      prefixBudget (parameters := parameters) position.val +
        stageBudget (parameters := parameters) (laterBuses (parameters := parameters))[position.val] := by
  unfold prefixBudget
  rw [List.take_succ_eq_append_getElem position.isLt, List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

theorem busTableAdvance_steps (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : BusMaskTable (parameters := parameters) rename flag position.val) :
    (busTableAdvance rename flag position table).checkedPrefix.steps =
      table.checkedPrefix.steps ++ (currentBusFromTable rename flag position table).steps := rfl

/-- The cumulative bound follows the actual source-prefix recursion and actual
concatenated checked traces, rather than an assumed generated proof program. -/
theorem buildBusPrefix_count (rename : Nat → Fin v) (flag : Bool) (count : Nat)
    (bound : count ≤ (laterBuses (parameters := parameters)).length) :
    (buildBusPrefix rename flag count bound).checkedPrefix.steps.length ≤ prefixBudget (parameters := parameters) count := by
  induction count with
  | zero =>
      change (firstBusTable (parameters := parameters) rename flag).checkedPrefix.steps.length ≤ _
      simpa [prefixBudget] using firstBusTable_count rename flag
  | succ count ih =>
      let position : Fin (laterBuses (parameters := parameters)).length := ⟨count, by omega⟩
      let prior := buildBusPrefix rename flag count (by omega)
      change (busTableAdvance rename flag position prior).checkedPrefix.steps.length ≤ _
      rw [busTableAdvance_steps, List.length_append]
      have one : prior.checkedPrefix.steps.length ≤ prefixBudget (parameters := parameters) count := ih (by omega)
      have two : (currentBusFromTable rename flag position prior).steps.length ≤
          stageBudget (parameters := parameters) (laterBuses (parameters := parameters))[position.val] :=
        (currentBusFromTable rename flag position prior).count
      have recurrence := prefixBudget_succ (parameters := parameters) position
      change prefixBudget (parameters := parameters) (count + 1) = _ at recurrence
      rw [recurrence]
      dsimp only [position] at two ⊢
      exact Nat.add_le_add one two

theorem stageBudget_uniform (bus : Fin parameters.buses) :
    stageBudget (parameters := parameters) bus ≤
      12 * parameters.channels * (2 + parameters.buses) + 38 * parameters.channels := by
  have filtered := List.length_filter_le (fun earlier : Fin parameters.buses => decide (earlier < bus))
    (List.finRange parameters.buses)
  simp only [List.length_finRange] at filtered
  exact Nat.add_le_add_right (Nat.mul_le_mul_left (12 * parameters.channels)
    (Nat.add_le_add_left filtered 2)) (38 * parameters.channels)

theorem sum_map_le_length_mul {α : Type} (values : List α) (cost : α → Nat) (limit : Nat)
    (bound : ∀ value ∈ values, cost value ≤ limit) : (values.map cost).sum ≤ values.length * limit := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      have one := bound value (by simp)
      have two := ih (fun item member => bound item (List.mem_cons_of_mem _ member))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- A uniform bound depends only on bus/channel counts and includes the seed.
It counts actual resolution inferences, separately from prefix copying costs. -/
theorem allBusMasks_count (rename : Nat → Fin v) (flag : Bool) :
    (allBusMasks (parameters := parameters) rename flag).checkedPrefix.steps.length ≤
      2 * parameters.channels + parameters.buses *
        (12 * parameters.channels * (2 + parameters.buses) + 38 * parameters.channels) := by
  have actual := buildBusPrefix_count rename flag (laterBuses (parameters := parameters)).length (Nat.le_refl _)
  have summed := sum_map_le_length_mul (laterBuses (parameters := parameters))
    (stageBudget (parameters := parameters)) _ (fun bus _ => stageBudget_uniform (parameters := parameters) bus)
  have length : (laterBuses (parameters := parameters)).length ≤ parameters.buses := by
    simpa only [laterBuses, List.length_finRange] using
      List.length_filter_le (fun bus : Fin parameters.buses => bus.val != 0) (List.finRange parameters.buses)
  have uniform := Nat.mul_le_mul_right
    (12 * parameters.channels * (2 + parameters.buses) + 38 * parameters.channels) length
  simp only [prefixBudget, List.take_length] at actual
  exact actual.trans (Nat.add_le_add_left (summed.trans uniform) (2 * parameters.channels))

@[simp] theorem pairedOr_unary (state : State v) (context : Clause (Fin v))
    (leftOut rightOut : Literal (Fin v)) (pairs : List (Literal (Fin v) × Literal (Fin v)))
    (nonempty : pairs ≠ [])
    (leftTree : AndTree state (negate leftOut) ((pairs.map Prod.fst).map negate))
    (rightTree : AndTree state (negate rightOut) ((pairs.map Prod.snd).map negate))
    (transfers : ∀ pair ∈ pairs, DirectionPair state context pair.1 pair.2)
    (one : pairs.length = 1) :
    (pairedOr state context leftOut rightOut pairs nonempty leftTree rightTree transfers).steps.length = 0 := by
  unfold pairedOr
  dsimp only
  simp only [List.length_append, guardedOr_unary, List.length_map, one, Nat.zero_add]

end Controller.NativeProof.SourceBusAdvance
