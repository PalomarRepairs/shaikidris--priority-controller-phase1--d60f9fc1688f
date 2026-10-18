module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestMarkerResetLoop

@[expose] public section

/-!
# Operational scope-marker collection

The collection phase installs a zero sentinel and tests each supplied channel
incidence using its emitted touch block. Fresh cells contribute one encoded
channel ID; repeated cells retain the existing touched stack. Marker addresses,
program blocks and word-width bounds are explicit inputs. Instruction emission
and traversal of the decoder representation have separate construction costs.
-/
namespace Controller.Cost.ForestMarkerCollect

open Controller.Decoder Controller.Cost.GateProgram
open Controller.Cost.ForestCounter Controller.Cost.ForestScopeMarkers
open Controller.Cost.ForestMarkerMachine Controller.Cost.ForestMarkerResetLoop

def sentinelCode (width : ℕ) : ForestCounter.Code width :=
  [.constant 0 (word width 0), .push 0]

@[simp] theorem sentinelCode_length (width : ℕ) : (sentinelCode width).length = 2 := rfl

/-- Two fetched instructions install the reset-loop sentinel. -/
theorem sentinel_install (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (address loaded temporary : Word width)
    (fits : base + 2 < 2 ^ width) (block : BlockAt program base (sentinelCode width)) :
    Execution program (counterState heap base address loaded temporary)
      ((counterState heap (base + 2) (word width 0) loaded temporary).frame [word width 0] [])
      2 (6 + heap.size) := by
  have first : program[base]? = some (.constant 0 (word width 0)) := by
    simpa [sentinelCode] using block 0 (by simp)
  have second : program[base + 1]? = some (.push 0) := by
    simpa [sentinelCode] using block 1 (by simp)
  have initial := address_transition program heap base 0 address loaded temporary (by omega) first
  have final := push_transition program heap (base + 1) (word width 0) loaded temporary
    (by omega) second
  have trace := Execution.cons initial (Execution.cons final (Execution.refl
    ((counterState heap (base + 2) (word width 0) loaded temporary).frame [word width 0] [])))
  convert trace using 1 <;> simp only [counterState_liveWords, State.frame_liveWords,
    List.length_cons, List.length_nil, Nat.add_zero] <;> omega

theorem touch_length_mono (state : MarkState n) (coordinate : Channel n) :
    state.touched.length ≤ (touch state coordinate).touched.length := by
  unfold touch
  split <;> simp

theorem touchAll_length_mono (state : MarkState n) (labels : List (Channel n)) :
    state.touched.length ≤ (touchAll state labels).touched.length := by
  induction labels generalizing state with
  | nil => exact Nat.le_refl _
  | cons coordinate rest ih =>
      exact (touch_length_mono state coordinate).trans (ih (touch state coordinate))

/-- The actual marked/fresh branch refines the logical marker update and encoded
stack. Registers zero through two are outputs; register three stays zero. -/
theorem touch_refines (program : Program width 4) (heap : Array (Word width))
    (base offset : ℕ) (state : MarkState n) (coordinate : Channel n)
    (address loaded temporary : Word width) (stack output : List (Word width))
    (stored : MarkersStored heap offset state) (well : WellFormed state)
    (fits : base + 9 < 2 ^ width) (addressFits : offset + coordinate.val < 2 ^ width)
    (oneFits : 1 < 2 ^ width)
    (block : BlockAt program base (touchBody width base (offset + coordinate.val) (coordinate.val + 1))) :
    ∃ finalAddress finalLoaded finalTemporary : Word width, ∃ ticks peak : ℕ,
      Execution program
        ((counterState heap base address loaded temporary).frame
          (encodedStack width state.touched ++ stack) output)
        ((counterState (touchHeap width offset heap coordinate) (base + 9)
          finalAddress finalLoaded finalTemporary).frame
          (encodedStack width (touch state coordinate).touched ++ stack) output) ticks peak ∧
      ticks = 5 + 2 * ((touch state coordinate).touched.length - state.touched.length) ∧
      peak ≤ 6 + heap.size + (touch state coordinate).touched.length +
        (stack.length + output.length) ∧
      WellFormed (touch state coordinate) ∧
      MarkersStored (touchHeap width offset heap coordinate) offset (touch state coordinate) := by
  have valid := stored.valid coordinate
  have representation := stored.held coordinate
  have read := readMark_stored width offset heap state stored oneFits coordinate
  have nextWell := touch_wellFormed state coordinate well
  have nextStored := touchHeap_stored width offset heap state stored oneFits coordinate
  by_cases marked : state.marked coordinate = true
  · have unchanged : touch state coordinate = state := by simp [touch, marked]
    have sameHeap : touchHeap width offset heap coordinate = heap := by
      simp only [touchHeap, read, marked, ite_true]
    have held : heap[offset + coordinate.val] = word width 1 := by
      simpa only [marked, ite_true] using representation
    have trace := marked_touch_execution_framed program heap base (offset + coordinate.val)
      (coordinate.val + 1) address loaded temporary (encodedStack width state.touched ++ stack)
      output fits addressFits oneFits valid held block
    refine ⟨word width (offset + coordinate.val), word width 1, word width 0, 5,
      5 + heap.size + ((encodedStack width state.touched ++ stack).length + output.length),
      ?_, ?_, ?_, nextWell, nextStored⟩
    · simpa only [sameHeap, unchanged] using trace
    · simp only [unchanged, Nat.sub_self, Nat.mul_zero, Nat.add_zero]
    · simp only [unchanged, encodedStack, List.length_append, List.length_map,
        List.length_cons, List.length_nil, Nat.add_zero]
      omega
  · have off : state.marked coordinate = false := Bool.eq_false_iff.mpr marked
    have touched : (touch state coordinate).touched = coordinate :: state.touched := by
      simp only [touch, off, Bool.false_eq_true, ite_false]
    have sameHeap : touchHeap width offset heap coordinate =
        heap.set (offset + coordinate.val) (word width 1) valid := by
      simp only [touchHeap, read, off, Bool.false_eq_true, ite_false, dite_eq_left valid]
    have held : heap[offset + coordinate.val] = word width 0 := by
      simpa only [off, Bool.false_eq_true, ite_false] using representation
    have trace := fresh_touch_execution_framed program heap base (offset + coordinate.val)
      (coordinate.val + 1) address loaded temporary (encodedStack width state.touched ++ stack)
      output fits addressFits valid held block
    refine ⟨word width (coordinate.val + 1), word width 0, word width 1, 7,
      6 + heap.size + ((encodedStack width state.touched ++ stack).length + output.length),
      ?_, ?_, ?_, nextWell, nextStored⟩
    · simpa only [sameHeap, touched, encodedStack, List.map_cons, List.cons_append] using trace
    · simp only [touched, List.length_cons]
      omega
    · simp only [touched, encodedStack, List.length_append, List.length_map,
        List.length_cons, List.length_nil, Nat.add_zero]
      omega

/-- Coverage of every emitted incidence block, including repeated labels. -/
def TouchBlocks (program : Program width 4) (base offset : ℕ) : List (Channel n) → Prop
  | [] => True
  | coordinate :: rest =>
      BlockAt program base (touchBody width base (offset + coordinate.val) (coordinate.val + 1)) ∧
        TouchBlocks program (base + 9) offset rest

def collectedHeap (width offset : ℕ) (heap : Array (Word width)) (labels : List (Channel n)) :
    Array (Word width) := labels.foldl (touchHeap width offset) heap

@[simp] theorem touchHeap_size (width offset : ℕ) (heap : Array (Word width))
    (coordinate : Channel n) : (touchHeap width offset heap coordinate).size = heap.size := by
  unfold touchHeap
  split
  · rfl
  · split <;> simp

@[simp] theorem collectedHeap_size (width offset : ℕ) (heap : Array (Word width))
    (labels : List (Channel n)) : (collectedHeap width offset heap labels).size = heap.size := by
  induction labels generalizing heap with
  | nil => rfl
  | cons coordinate rest ih =>
      exact (ih (touchHeap width offset heap coordinate)).trans
        (touchHeap_size width offset heap coordinate)

/-- Genuine fetched touch bodies compose over the supplied incidence list.
The represented marker set may be much smaller than this list. -/
theorem list_refines (program : Program width 4) (heap : Array (Word width))
    (base offset : ℕ) (state : MarkState n) (labels : List (Channel n))
    (address loaded temporary : Word width) (stack output : List (Word width))
    (stored : MarkersStored heap offset state) (well : WellFormed state)
    (fits : base + 9 * labels.length < 2 ^ width)
    (addressFits : ∀ coordinate ∈ labels, offset + coordinate.val < 2 ^ width)
    (oneFits : 1 < 2 ^ width) (blocks : TouchBlocks program base offset labels) :
    ∃ finalAddress finalLoaded finalTemporary : Word width, ∃ ticks peak : ℕ,
      Execution program
        ((counterState heap base address loaded temporary).frame
          (encodedStack width state.touched ++ stack) output)
        ((counterState (collectedHeap width offset heap labels) (base + 9 * labels.length)
          finalAddress finalLoaded finalTemporary).frame
          (encodedStack width (touchAll state labels).touched ++ stack) output) ticks peak ∧
      ticks = 5 * labels.length + 2 * ((touchAll state labels).touched.length - state.touched.length) ∧
      peak ≤ 6 + heap.size + (touchAll state labels).touched.length +
        (stack.length + output.length) ∧
      WellFormed (touchAll state labels) ∧
      MarkersStored (collectedHeap width offset heap labels) offset (touchAll state labels) := by
  induction labels generalizing heap base state address loaded temporary with
  | nil =>
      refine ⟨address, loaded, temporary, 0,
        ((counterState heap base address loaded temporary).frame
          (encodedStack width state.touched ++ stack) output).liveWords,
        ?_, ?_, ?_, well, stored⟩
      · simpa only [collectedHeap, touchAll, List.foldl_nil, List.length_nil,
          Nat.mul_zero, Nat.add_zero] using Execution.refl
            ((counterState heap base address loaded temporary).frame
              (encodedStack width state.touched ++ stack) output)
      · simp [touchAll]
      · simp only [touchAll, List.foldl_nil, framed_counterState_liveWords,
          encodedStack, List.length_append, List.length_map, List.length_cons,
          List.length_nil, Nat.add_zero]
        omega
  | cons coordinate rest ih =>
      obtain ⟨a, l, t, firstTicks, firstPeak, first, firstCost, firstBound, nextWell, nextStored⟩ :=
        touch_refines program heap base offset state coordinate address loaded temporary stack output
          stored well (by simp only [List.length_cons] at fits; omega)
          (addressFits coordinate (by simp)) oneFits blocks.1
      have laterFits : base + 9 + 9 * rest.length < 2 ^ width := by
        simp only [List.length_cons] at fits
        omega
      obtain ⟨fa, fl, ft, tailTicks, tailPeak, tail, tailCost, tailBound, finalWell, finalStored⟩ :=
        ih (touchHeap width offset heap coordinate) (base + 9) (touch state coordinate) a l t
          nextStored nextWell laterFits (by
            intro current member
            exact addressFits current (by simp [member])) blocks.2
      have joined := first.append tail
      have initialMono := touch_length_mono state coordinate
      have finalMono := touchAll_length_mono (touch state coordinate) rest
      refine ⟨fa, fl, ft, firstTicks + tailTicks, max firstPeak tailPeak,
        ?_, ?_, ?_, finalWell, finalStored⟩
      · simpa only [collectedHeap, touchAll, List.foldl_cons, List.length_cons,
          Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using joined
      · change firstTicks + tailTicks =
          5 * (rest.length + 1) +
            2 * ((touchAll (touch state coordinate) rest).touched.length - state.touched.length)
        omega
      · change max firstPeak tailPeak ≤
          6 + heap.size + (touchAll (touch state coordinate) rest).touched.length +
            (stack.length + output.length)
        rw [touchHeap_size] at tailBound
        exact max_le (by omega) tailBound

/-- Sentinel installation and all emitted touch bodies form one executable
collection phase with no hidden initial touched stack. -/
theorem collect_from_empty (program : Program width 4) (heap : Array (Word width))
    (base offset : ℕ) (labels : List (Channel n))
    (address loaded temporary : Word width) (stack output : List (Word width))
    (stored : MarkersStored heap offset (ForestScopeMarkers.empty : MarkState n))
    (fits : base + 2 + 9 * labels.length < 2 ^ width)
    (addressFits : ∀ coordinate ∈ labels, offset + coordinate.val < 2 ^ width)
    (oneFits : 1 < 2 ^ width)
    (sentinel : BlockAt program base (sentinelCode width))
    (blocks : TouchBlocks program (base + 2) offset labels) :
    ∃ finalAddress finalLoaded finalTemporary : Word width, ∃ ticks peak : ℕ,
      Execution program ((counterState heap base address loaded temporary).frame stack output)
        ((counterState (collectedHeap width offset heap labels) (base + 2 + 9 * labels.length)
          finalAddress finalLoaded finalTemporary).frame
          (encodedStack width (touchAll ForestScopeMarkers.empty labels).touched ++ stack) output) ticks peak ∧
      ticks = 2 + 5 * labels.length + 2 * (touchAll ForestScopeMarkers.empty labels).touched.length ∧
      ticks ≤ 7 * labels.length + 2 ∧
      peak ≤ 6 + heap.size + (touchAll ForestScopeMarkers.empty labels).touched.length +
        (stack.length + output.length) ∧
      WellFormed (touchAll ForestScopeMarkers.empty labels) ∧
      MarkersStored (collectedHeap width offset heap labels) offset
        (touchAll ForestScopeMarkers.empty labels) := by
  have initial := (sentinel_install program heap base address loaded temporary
    (by omega) sentinel).frame stack output
  obtain ⟨fa, fl, ft, tailTicks, tailPeak, tail, tailCost, tailBound, finalWell, finalStored⟩ :=
    list_refines program heap (base + 2) offset ForestScopeMarkers.empty labels
      (word width 0) loaded temporary stack output stored empty_wellFormed fits addressFits oneFits blocks
  have boundary :
      ((counterState heap (base + 2) (word width 0) loaded temporary).frame
        [word width 0] []).frame stack output =
      (counterState heap (base + 2) (word width 0) loaded temporary).frame
        (encodedStack width (ForestScopeMarkers.empty : MarkState n).touched ++ stack) output := by
    simp only [State.frame, counterState, encodedStack, ForestScopeMarkers.empty, List.map_nil,
      List.nil_append, List.append_nil]
  rw [boundary] at initial
  have joined := initial.append tail
  have countBound := touchAll_length_le (ForestScopeMarkers.empty : MarkState n) labels
  simp only [show (ForestScopeMarkers.empty : MarkState n).touched.length = 0 from rfl,
    Nat.zero_add, Nat.sub_zero] at countBound tailCost
  refine ⟨fa, fl, ft, 2 + tailTicks,
    max (6 + heap.size + (stack.length + output.length)) tailPeak,
    joined, ?_, ?_, ?_, finalWell, finalStored⟩
  · omega
  · omega
  · exact max_le (by omega) tailBound

end Controller.Cost.ForestMarkerCollect
