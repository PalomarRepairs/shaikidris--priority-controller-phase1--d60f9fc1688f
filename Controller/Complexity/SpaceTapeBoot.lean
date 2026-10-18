module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceTapeRun

@[expose] public section

/-! Executed initialization of every ordinary work tape from an all-blank
tape. The fixed bank enumeration is part of finite control. -/
namespace Controller.Complexity.SpaceTapeBoot
open SpaceTapeMachine SpaceTapeRun

def prepared (enumeration : Fin n ≃ K) (input : List Bool) (index : Fin (n+1)) : SpaceTapeMachine.State n K Q :=
  ⟨some (.init index),SpaceInputTape.encode (ReadOnlyInput.start input),
    fun port => if (enumeration.symm port).val < index.val then SpaceWorkTape.encode [] else SpaceWorkTape.blank,
    fun port => if (enumeration.symm port).val < index.val then 1 else 0,[]⟩

theorem within (enumeration : Fin n ≃ K) (input : List Bool) (index : Fin (n+1)) :
    Within 2 (prepared enumeration input index : SpaceTapeMachine.State n K Q) := by
  intro port
  simp only [prepared]
  split <;> constructor <;> omega

theorem zero (enumeration : Fin n ≃ K) (input : List Bool) :
    prepared enumeration input ⟨0,by omega⟩=(SpaceTapeMachine.initial input : SpaceTapeMachine.State n K Q) := by
  simp [prepared,SpaceTapeMachine.initial]

theorem next [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (input : List Bool) (index : Fin (n+1)) (available : index.val<n) :
    SpaceTapeMachine.step enumeration program (prepared enumeration input index)=
      some (prepared enumeration input ⟨index.val+1,by omega⟩) := by
  simp only [SpaceTapeMachine.step,prepared,Option.map_some,delta,available,↓reduceDIte,
    apply,Option.elim_some,Option.elim_none,operate,shift]
  congr 2
  · funext port
    by_cases same : port=enumeration ⟨index.val,available⟩
    · subst port
      simp [SpaceWorkTape.initialization]
    · have different : (enumeration.symm port).val≠index.val := by
        intro equality
        have : enumeration.symm port=⟨index.val,available⟩ := Fin.ext equality
        exact same (by simpa using congrArg enumeration this)
      simp only [Function.update_of_ne same]
      have unchanged : ((enumeration.symm port).val < index.val) ↔ ((enumeration.symm port).val < index.val+1) := by omega
      simp [unchanged]
  · funext port
    by_cases same : port=enumeration ⟨index.val,available⟩
    · subst port; simp
    · have different : (enumeration.symm port).val≠index.val := by
        intro equality
        have : enumeration.symm port=⟨index.val,available⟩ := Fin.ext equality
        exact same (by simpa using congrArg enumeration this)
      simp only [Function.update_of_ne same]
      have unchanged : ((enumeration.symm port).val < index.val) ↔ ((enumeration.symm port).val < index.val+1) := by omega
      simp [unchanged]

theorem finish [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q) (input : List Bool) :
    SpaceTapeMachine.step enumeration program (prepared enumeration input ⟨n,by omega⟩)=
      some (configuration (SpaceMachine.initial program input)) := by
  simp only [SpaceTapeMachine.step,prepared,Option.map_some,delta,Nat.lt_irrefl,↓reduceDIte,
    apply,Option.elim_none,configuration,SpaceMachine.initial,Option.map_some]
  congr 2 <;> funext port <;> simp [(enumeration.symm port).isLt]

theorem suffix [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q) (input : List Bool)
    (remaining : Nat) (index : Fin (n+1)) (count : index.val+remaining=n) :
    Run enumeration program 2 (prepared enumeration input index)
      (configuration (SpaceMachine.initial program input)) (remaining+1) := by
  induction remaining generalizing index with
  | zero =>
    have same : index=⟨n,by omega⟩ := Fin.ext (by simpa using count)
    rw [same]
    exact Run.cons (finish enumeration program input) (within enumeration input _)
      (Run.refl (configuration_within _ 2 (by intro port; simp [SpaceMachine.initial])))
  | succ remaining ih =>
    have available : index.val<n := by omega
    have later := ih ⟨index.val+1,by omega⟩ (by change index.val+1+remaining=n; omega)
    exact Run.cons (next enumeration program input index available) (within enumeration input _) later

theorem execution [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q) (input : List Bool) :
    Run enumeration program 2 (SpaceTapeMachine.initial input)
      (configuration (SpaceMachine.initial program input)) (n+1) := by
  simpa only [zero,Nat.zero_add] using suffix enumeration program input n ⟨0,by omega⟩ (by simp)

end Controller.Complexity.SpaceTapeBoot
