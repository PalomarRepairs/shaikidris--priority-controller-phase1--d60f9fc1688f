module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.OpcodeDispatch
public import Controller.Complexity.BranchBody
public import Controller.Complexity.ArithmeticBody
public import Controller.Complexity.HaltBody
public import Controller.Complexity.StoreBody

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! One fixed opcode table contains the thirteen actual native instruction
bodies. The remaining three four-bit tags and short tags enter an explicit
error program. No word width, register index or operand is compiled into code. -/
namespace Controller.Complexity.BodyTable
open StackMachine WordReader
open scoped BigOperators

def HaltLabel : Type := StateReader.LabelsOf HaltBody.program
instance haltFintype : Fintype HaltLabel := inferInstanceAs (Fintype (StateReader.LabelsOf HaltBody.program))

def BodyLabel (tag : Fin 16) : Type := match tag.val with
  | 0 => ConstantBody.Label
  | 1 => CopyBody.Label
  | 2 => ArithmeticBody.Label false
  | 3 => ArithmeticBody.Label true
  | 4 => LoadBody.Label
  | 5 => StoreBody.Label
  | 6 => AllocateBody.Label
  | 7 => ReleaseBody.Label
  | 8 => PrependBody.Label
  | 9 => PopBody.Label
  | 10 => PrependBody.Label
  | 11 => BranchBody.Label
  | 12 => HaltLabel
  | _ => Fin 2

instance bodyFintype (tag : Fin 16) : Fintype (BodyLabel tag) := match tag with
  | ⟨0,_⟩ => inferInstanceAs (Fintype ConstantBody.Label)
  | ⟨1,_⟩ => inferInstanceAs (Fintype CopyBody.Label)
  | ⟨2,_⟩ => inferInstanceAs (Fintype (ArithmeticBody.Label false))
  | ⟨3,_⟩ => inferInstanceAs (Fintype (ArithmeticBody.Label true))
  | ⟨4,_⟩ => inferInstanceAs (Fintype LoadBody.Label)
  | ⟨5,_⟩ => inferInstanceAs (Fintype StoreBody.Label)
  | ⟨6,_⟩ => inferInstanceAs (Fintype AllocateBody.Label)
  | ⟨7,_⟩ => inferInstanceAs (Fintype ReleaseBody.Label)
  | ⟨8,_⟩ => inferInstanceAs (Fintype PrependBody.Label)
  | ⟨9,_⟩ => inferInstanceAs (Fintype PopBody.Label)
  | ⟨10,_⟩ => inferInstanceAs (Fintype PrependBody.Label)
  | ⟨11,_⟩ => inferInstanceAs (Fintype BranchBody.Label)
  | ⟨12,_⟩ => inferInstanceAs (Fintype HaltLabel)
  | ⟨_n+13,_⟩ => inferInstanceAs (Fintype (Fin 2))

def reject : Program (Fin 31) (Fin 2) where
  main := 0
  code label := if label=0 then .push none false 1 else .halt

def family (tag : Fin 16) : Program (Fin 31) (BodyLabel tag) := match tag with
  | ⟨0,_⟩ => ConstantBody.program
  | ⟨1,_⟩ => CopyBody.program
  | ⟨2,_⟩ => ArithmeticBody.program false
  | ⟨3,_⟩ => ArithmeticBody.program true
  | ⟨4,_⟩ => LoadBody.program
  | ⟨5,_⟩ => StoreBody.program
  | ⟨6,_⟩ => AllocateBody.program
  | ⟨7,_⟩ => ReleaseBody.program
  | ⟨8,_⟩ => PrependBody.program false
  | ⟨9,_⟩ => PopBody.program
  | ⟨10,_⟩ => PrependBody.program true
  | ⟨11,_⟩ => BranchBody.program
  | ⟨12,_⟩ => HaltBody.program
  | ⟨_n+13,_⟩ => reject

def Label : Type := OpcodeDispatch.Label BodyLabel
instance labelFintype : Fintype Label := inferInstanceAs (Fintype ((Fin 4 × Fin 16) ⊕ (Σ tag, BodyLabel tag)))
def program : Program (Fin 31) Label := OpcodeDispatch.program family 15

def nativeTag (bound : registers ≤ 2^width) (instruction : Controller.Cost.Instruction width registers) : Fin 16 :=
  ⟨(InstructionCodec.fields bound instruction).1,InstructionCodec.fields_tag_lt bound instruction⟩

theorem selection (input : Port → List Bool) (tag : Fin 16) (stored : input (some 13)=(Encoding.bits 4 tag.val).reverse) :
    ∃ peak, Execution program ⟨some program.main,input⟩
      ⟨some (OpcodeDispatch.enter tag (family tag).main),Function.update input (some 13) []⟩ 4 peak :=
  OpcodeDispatch.selection family 15 tag input stored

theorem execution (input output : Port → List Bool) (tag : Fin 16) (stored : input (some 13)=(Encoding.bits 4 tag.val).reverse) {ticks peak}
    (trace : Execution (family tag) ⟨some (family tag).main,Function.update input (some 13) []⟩ ⟨none,output⟩ ticks peak) :
    ∃ totalPeak, Execution program ⟨some program.main,input⟩ ⟨none,output⟩ (4+ticks) totalPeak ∧
      totalPeak ≤ OpcodeDispatch.size input+(4+ticks) := OpcodeDispatch.execution family 15 tag input output stored trace

theorem reject_execution (input : Port → List Bool) :
    ∃ peak, Execution reject ⟨some reject.main,input⟩ ⟨none,Function.update input none (false :: input none)⟩ 2 peak := by
  have first : step reject ⟨some reject.main,input⟩=some ⟨some 1,Function.update input none (false :: input none)⟩ := rfl
  have last : step reject ⟨some 1,Function.update input none (false :: input none)⟩=some ⟨none,Function.update input none (false :: input none)⟩ := rfl
  exact ⟨_,Execution.cons first (Execution.cons last (Execution.refl _))⟩

def bodyCount (tag : Fin 16) : Nat := match tag.val with
  | 0 => 785 | 1 => 967 | 2 => 1278 | 3 => 1272 | 4 => 1162 | 5 => 1176
  | 6 => 769 | 7 => 520 | 8 => 724 | 9 => 782 | 10 => 724 | 11 => 977 | 12 => 405 | _ => 2

theorem halt_card : Fintype.card HaltLabel=405 := by
  have original : Fintype.card (StateReader.LabelsOf HaltBody.program)=405 := by
    simp only [StateReader.LabelsOf,Fintype.card_sum,PcAdvance.canonical_card,Fintype.card_fin,Nat.reduceAdd]
  have same : Fintype.card HaltLabel=Fintype.card (StateReader.LabelsOf HaltBody.program) :=
    @Fintype.card_congr HaltLabel (StateReader.LabelsOf HaltBody.program) _ _ (Equiv.refl _)
  exact same.trans original

theorem body_card (tag : Fin 16) : Fintype.card (BodyLabel tag)=bodyCount tag := by
  fin_cases tag
  · exact ConstantBody.canonical_card
  · exact CopyBody.canonical_card
  · exact ArithmeticBody.canonical_card false
  · exact ArithmeticBody.canonical_card true
  · exact LoadBody.canonical_card
  · exact StoreBody.canonical_card
  · exact AllocateBody.canonical_card
  · exact ReleaseBody.canonical_card
  · exact PrependBody.canonical_card
  · exact PopBody.canonical_card
  · exact PrependBody.canonical_card
  · exact BranchBody.canonical_card
  · exact halt_card
  · exact Fintype.card_fin 2
  · exact Fintype.card_fin 2
  · exact Fintype.card_fin 2

theorem bodies_card : (∑ tag : Fin 16,Fintype.card (BodyLabel tag))=11547 := by
  calc
    _ = ∑ tag : Fin 16,bodyCount tag := Finset.sum_congr rfl (fun tag _ => body_card tag)
    _ = 11547 := by decide

theorem canonical_card : Fintype.card Label=11611 := by
  have split : Fintype.card Label=4*16+∑ tag : Fin 16,Fintype.card (BodyLabel tag) := by
    change Fintype.card ((Fin 4 × Fin 16) ⊕ (Σ tag, BodyLabel tag))=_
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_sigma]
  rw [bodies_card] at split
  exact split

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 104499 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.BodyTable
