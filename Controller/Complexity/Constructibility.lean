module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.TapeTransducer

@[expose] public section

/-! Unary-input, canonical-binary-output constructibility on ordinary finite
multitape machines. Bounds are eventual multiplicative bounds; all input
sizes must terminate. Space counts actual visited work cells, excluding the
immutable input and append-only output tapes. -/
namespace Controller.Complexity.Constructibility
open TapeTransducer
open scoped BigOperators

def unary (size : Nat) : List Bool := List.replicate size true

def TimeConstructible (bound : Nat → Nat) : Prop :=
  ∃ (banks labels : Nat) (machine : Machine (Fin banks) (Fin labels)) (constant threshold : Nat),
    ∀ size, ∃ final ticks,
      Nonempty (StateTransition.EvalsToInTime (step machine) (initial machine (unary size)) (some final) ticks) ∧
      final.pc=none ∧ final.output.reverse=(bound size).bits ∧
      (threshold ≤ size → ticks ≤ constant*bound size)

def SpaceConstructible (bound : Nat → Nat) : Prop :=
  ∃ (banks labels : Nat) (machine : Machine (Fin banks) (Fin labels)) (constant threshold : Nat),
    ∀ size, ∃ final ticks cells,
      Covered machine cells (initialAnnotated machine (unary size)) final ticks ∧
      final.configuration.pc=none ∧ final.configuration.output.reverse=(bound size).bits ∧
      (threshold ≤ size → (∑ port, (cells port).card) ≤ constant*bound size)

theorem TimeConstructible.unary_output {bound : Nat → Nat} (constructible : TimeConstructible bound) :
    ∃ (banks labels : Nat) (machine : Machine (Fin banks) (Fin labels)), ∀ size, ∃ final ticks,
      Nonempty (StateTransition.EvalsToInTime (step machine) (initial machine (unary size)) (some final) ticks) ∧
      final.pc=none ∧ final.output.reverse=(bound size).bits := by
  obtain ⟨banks,labels,machine,constant,threshold,actual⟩ := constructible
  refine ⟨banks,labels,machine,fun size => ?_⟩
  obtain ⟨final,ticks,trace,halted,output,time⟩ := actual size
  exact ⟨final,ticks,trace,halted,output⟩

theorem SpaceConstructible.unary_output {bound : Nat → Nat} (constructible : SpaceConstructible bound) :
    ∃ (banks labels : Nat) (machine : Machine (Fin banks) (Fin labels)), ∀ size, ∃ final ticks,
      Nonempty (StateTransition.EvalsToInTime (step machine) (initial machine (unary size)) (some final) ticks) ∧
      final.pc=none ∧ final.output.reverse=(bound size).bits := by
  obtain ⟨banks,labels,machine,constant,threshold,actual⟩ := constructible
  refine ⟨banks,labels,machine,fun size => ?_⟩
  obtain ⟨final,ticks,cells,trace,halted,output,space⟩ := actual size
  exact ⟨final.configuration,ticks,trace.evals,halted,output⟩

def oneMachine : Machine (Fin 0) (Fin 2) where
  main := 0
  delta label _ _ := ⟨if label.val=0 then some 1 else none,fun _ => none,fun _ => none,
    none,if label.val=0 then some true else none⟩

def oneFinal (input : List Bool) : Configuration (Fin 0) (Fin 2) :=
  ⟨none,SpaceInputTape.encode (ReadOnlyInput.start input),fun _ => SpaceWorkTape.blank,[true]⟩

theorem one_execution (input : List Bool) :
    Nonempty (StateTransition.EvalsToInTime (step oneMachine) (initial oneMachine input) (some (oneFinal input)) 2) := by
  let middle : Configuration (Fin 0) (Fin 2) :=
    ⟨some 1,SpaceInputTape.encode (ReadOnlyInput.start input),fun _ => SpaceWorkTape.blank,[true]⟩
  have first : StateTransition.EvalsToInTime (step oneMachine) (initial oneMachine input) (some middle) 1 :=
    ⟨⟨1,rfl⟩,le_rfl⟩
  have last : StateTransition.EvalsToInTime (step oneMachine) middle (some (oneFinal input)) 1 :=
    ⟨⟨1,rfl⟩,le_rfl⟩
  exact ⟨StateTransition.EvalsToInTime.trans _ 1 1 _ _ _ first last⟩

theorem one_covered (input : List Bool) :
    Covered oneMachine (fun _ => ∅) (initialAnnotated oneMachine input) ⟨oneFinal input,fun _ => 0⟩ 2 := by
  let middle : Annotated (Fin 0) (Fin 2) :=
    ⟨⟨some 1,SpaceInputTape.encode (ReadOnlyInput.start input),fun _ => SpaceWorkTape.blank,[true]⟩,fun _ => 0⟩
  have first : markedStep oneMachine (initialAnnotated oneMachine input)=some middle := rfl
  have last : markedStep oneMachine middle=some ⟨oneFinal input,fun _ => 0⟩ := rfl
  exact Covered.cons first (fun port => Fin.elim0 port)
    (Covered.cons last (fun port => Fin.elim0 port) (Covered.refl (fun port => Fin.elim0 port)))

theorem time_one : TimeConstructible (fun _ => 1) := by
  refine ⟨0,2,oneMachine,2,0,fun size => ?_⟩
  exact ⟨oneFinal (unary size),2,one_execution _,rfl,by simp [oneFinal,Nat.one_bits],by intro _; rfl⟩

theorem space_one : SpaceConstructible (fun _ => 1) := by
  refine ⟨0,2,oneMachine,0,0,fun size => ?_⟩
  exact ⟨_,2,_,one_covered (unary size),rfl,by simp [oneFinal,Nat.one_bits],by intro _; simp⟩

end Controller.Complexity.Constructibility
