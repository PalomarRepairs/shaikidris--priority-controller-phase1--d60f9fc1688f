module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.CheckedWordField

public import Mathlib.Tactic.Ring

@[expose] public section

/-! A fixed binary-stack state reader joins checked registers, three data
fields, a checked singleton PC and the exact halt/EOF check. Successful field
storage conserves the live-bank sum; guards stop at the first rejected field. -/
namespace Controller.Complexity.StateReader
open StackMachine WordReader
open scoped BigOperators

inductive Field where
  | registers | heap | stack | output | control
  deriving DecidableEq, Repr

abbrev LabelsOf {Q : Type} (_ : Program (Fin 31) Q) := Q

def Field.slot : Field → Fin 31
  | .registers => 21
  | .heap => 22
  | .stack => 23
  | .output => 24
  | .control => 25

theorem Field.slot_high (field : Field) : 21 ≤ field.slot.val := by cases field <;> decide
theorem Field.slot_low (field : Field) : field.slot.val < 26 := by cases field <;> decide

def Field.Label : Field → Type
  | .registers => LabelsOf CheckedWordField.registerProgram
  | .control => LabelsOf CheckedWordField.pcProgram
  | _ => LabelsOf (WordFieldReader.program 22)

instance (field : Field) : Fintype field.Label := by cases field <;> dsimp [Field.Label,LabelsOf] <;> infer_instance

def Field.program : (field : Field) → Program (Fin 31) field.Label
  | .registers => CheckedWordField.registerProgram
  | .heap => WordFieldReader.program 22
  | .stack => WordFieldReader.program 23
  | .output => WordFieldReader.program 24
  | .control => CheckedWordField.pcProgram

def Field.read (field : Field) (width registers : Nat) (input : List Bool) : Option (List (Controller.Cost.Word width) × List Bool) :=
  match field with
  | .registers => CheckedWordField.readField (fun count => decide (count=registers)) width input
  | .control => CheckedWordField.readField (fun count => decide (count=1)) width input
  | _ => Encoding.readFramedWords width input

open CheckedWordField (mass)

def work : List (Fin 31) := [1,2,10,11,12,16,17,20]

structure Ready (input : Port → List Bool) (width registers : Nat) (fields : List Field) : Prop where
  status : input none=[]
  savedWidth : input (some 8)=List.replicate width true
  savedRegisters : input (some 9)=List.replicate registers true
  workspace : ∀ index ∈ work, input (some index)=[]
  targets : ∀ field ∈ fields, input (some field.slot)=[]
  haltEmpty : input (some 26)=[]

theorem Ready.mass (input : Port → List Bool) (ready : Ready input width registers fields) :
    mass input=(input (some 0)).length+ambientBits input := by
  have entry := WordFieldReader.ready_bank input ready.status (ready.workspace 1 (by decide)) (ready.workspace 2 (by decide))
  have total := bank_live input (none : Option Unit) [] (input (some 0)) []
  rw [entry] at total
  simpa only [live,CheckedWordField.mass,List.length_nil,Nat.zero_add,Nat.add_zero] using total

theorem slot_ne (field : Field) (index : Fin 31) (low : index.val < 21) : field.slot ≠ index := by
  have high := field.slot_high
  intro same
  rw [same] at high
  omega

theorem slot_ne_halt (field : Field) : field.slot ≠ 26 := by
  have low := field.slot_low
  intro same
  simp [same] at low

theorem Ready.packet (input : Port → List Bool) (field : Field) (fields : List Field)
    (ready : Ready input width registers (field :: fields)) (distinct : (field.slot :: fields.map Field.slot).Nodup)
    (words : List (Controller.Cost.Word width)) (suffix : List Bool) :
    Ready (WordFieldReader.packet input field.slot width words suffix) width registers fields := by
  have others := List.nodup_cons.mp distinct
  refine ⟨by simp [WordFieldReader.packet_at input field.slot field.slot_high],?_,?_,?_,?_,?_⟩
  · simpa [WordFieldReader.packet_at input field.slot field.slot_high,Ne.symm (slot_ne field 8 (by decide))] using ready.savedWidth
  · simpa [WordFieldReader.packet_at input field.slot field.slot_high,Ne.symm (slot_ne field 9 (by decide))] using ready.savedRegisters
  · intro index member
    have low : index.val < 21 := by
      simp [work] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have clean := ready.workspace index member
    by_cases one : index=1 <;> by_cases two : index=2 <;> by_cases zero : index=0 <;>
      simp_all [work,WordFieldReader.packet_at input field.slot field.slot_high,Ne.symm (slot_ne field index low)]
  · intro next member
    have unequal : next.slot ≠ field.slot := by
      intro same
      have inside : field.slot ∈ fields.map Field.slot := by rw [← same]; exact List.mem_map.mpr ⟨next,member,rfl⟩
      exact others.1 inside
    simpa [WordFieldReader.packet_at input field.slot field.slot_high,unequal,
      slot_ne next 0 (by decide),slot_ne next 1 (by decide),slot_ne next 2 (by decide)] using ready.targets next (by simp [member])
  · simpa [WordFieldReader.packet_at input field.slot field.slot_high,Ne.symm (slot_ne_halt field)] using ready.haltEmpty

def Label : List Field → Type
  | [] => Fin 7
  | field :: fields => field.Label ⊕ Option (Label fields)

instance labelFintype (fields : List Field) : Fintype (Label fields) := by
  induction fields with
  | nil => dsimp [Label]; infer_instance
  | cons field fields ih => dsimp [Label]; infer_instance

def program : (fields : List Field) → Program (Fin 31) (Label fields)
  | [] => StateShape.tailProgram
  | field :: fields => GuardedLink.program field.program (program fields) none Option.isNone

def read (width registers : Nat) : List Field → List Bool → Option (List (List (Controller.Cost.Word width)) × Bool)
  | [],input => (StateShape.decodeTail input).map fun halt => ([],halt)
  | field :: fields,input => do
    let (words,suffix) ← field.read width registers input
    let (rest,halt) ← read width registers fields suffix
    return (words :: rest,halt)

def fieldsBank (frame : Port → List Bool) (width : Nat) : List Field → List (List (Controller.Cost.Word width)) → Port → List Bool
  | field :: fields,words :: rest => fieldsBank (Function.update frame (some field.slot) (Encoding.encodeWords width words)) width fields rest
  | _,_ => frame

def store (frame : Port → List Bool) (width : Nat) (fields : List Field) (values : List (List (Controller.Cost.Word width))) (halt : Bool) :=
  StateShape.tail (fieldsBank frame width fields values) [] [] [halt]

def cost (size : Nat) := 16*size^2+40*size+40

theorem field_read_sound (field : Field) (width registers : Nat) (source : List Bool)
    (words : List (Controller.Cost.Word width)) (suffix : List Bool)
    (decoded : field.read width registers source=some (words,suffix)) :
    source=Encoding.encodeWords width words++suffix := by
  cases field with
  | heap | stack | output => exact InstructionFrontend.framed_sound width source words suffix decoded
  | registers | control =>
    simp only [Field.read,CheckedWordField.readField] at decoded
    cases parsed : Encoding.readFramedWords width source with
    | none => simp [parsed] at decoded
    | some pair =>
      rcases pair with ⟨values,rest⟩
      simp only [parsed,Bind.bind,Option.bind] at decoded
      split at decoded
      · simp only [Option.some.injEq,Prod.mk.injEq] at decoded
        rcases decoded with ⟨rfl,rfl⟩
        exact InstructionFrontend.framed_sound width source _ _ parsed
      · simp at decoded

theorem fieldsBank_source (frame : Port → List Bool) (width : Nat) (fields : List Field)
    (values : List (List (Controller.Cost.Word width))) (source : List Bool) :
    fieldsBank (Function.update frame (some 0) source) width fields values=
      Function.update (fieldsBank frame width fields values) (some 0) source := by
  induction fields generalizing frame values with
  | nil => rfl
  | cons field fields ih =>
    cases values with
    | nil => rfl
    | cons words values =>
      simp only [fieldsBank]
      rw [Function.update_comm (by simpa using Ne.symm (slot_ne field 0 (by decide))),ih]

theorem store_source (frame : Port → List Bool) (width : Nat) (fields : List Field)
    (values : List (List (Controller.Cost.Word width))) (source : List Bool) (halt : Bool) :
    store (Function.update frame (some 0) source) width fields values halt=store frame width fields values halt := by
  rw [store,fieldsBank_source]
  funext address
  by_cases hs : address=none <;> by_cases hi : address=some 0 <;> by_cases hh : address=some 26 <;> simp_all [store,StateShape.tail_at]

theorem packet_eq (input : Port → List Bool) (field : Field) (ready : Ready input width registers pending)
    (words : List (Controller.Cost.Word width)) (suffix : List Bool) :
    WordFieldReader.packet input field.slot width words suffix=
      Function.update (Function.update input (some field.slot) (Encoding.encodeWords width words)) (some 0) suffix := by
  have h₀ := slot_ne field 0 (by decide)
  have h₁ := slot_ne field 1 (by decide)
  have h₂ := slot_ne field 2 (by decide)
  funext address
  by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
    by_cases ht : address=some 2 <;> by_cases hd : address=some field.slot <;>
    simp_all [WordFieldReader.packet_at input field.slot field.slot_high,ready.status,
      ready.workspace 1 (by decide),ready.workspace 2 (by decide),Ne.symm (slot_ne field 0 (by decide)),
      Ne.symm (slot_ne field 1 (by decide)),Ne.symm (slot_ne field 2 (by decide))]

theorem store_packet (input : Port → List Bool) (field : Field) (fields : List Field) (ready : Ready input width registers pending)
    (words : List (Controller.Cost.Word width)) (suffix : List Bool) (values : List (List (Controller.Cost.Word width))) (halt : Bool) :
    store (WordFieldReader.packet input field.slot width words suffix) width fields values halt=
      store input width (field :: fields) (words :: values) halt := by
  rw [packet_eq input field ready words suffix,store_source]
  rfl

theorem packet_mass (input : Port → List Bool) (field : Field) (fields : List Field)
    (ready : Ready input width registers (field :: fields)) (words : List (Controller.Cost.Word width)) (suffix : List Bool)
    (decoded : field.read width registers (input (some 0))=some (words,suffix)) :
    mass (WordFieldReader.packet input field.slot width words suffix)=mass input := by
  rw [CheckedWordField.packet_mass input field.slot field.slot_high words suffix (ready.targets field (by simp)),ready.mass]
  rw [← field_read_sound field width registers (input (some 0)) words suffix decoded]

theorem normal_total (input : Port → List Bool) (slot : Fin 31) (high : 21 ≤ slot.val)
    (ready : Ready input width registers fields) (empty : input (some slot)=[]) :
    ∃ ticks peak output, Execution (WordFieldReader.program slot) ⟨some (WordFieldReader.program slot).main,input⟩
      ⟨none,output⟩ ticks peak ∧ ticks ≤ cost (mass input) ∧
      Option.isNone ((output none).head?)=(Encoding.readFramedWords width (input (some 0))).isSome ∧
      (∀ words suffix, Encoding.readFramedWords width (input (some 0))=some (words,suffix) →
        output=WordFieldReader.packet input slot width words suffix) := by
  obtain ⟨ticks,peak,trace,timeBound,spaceBound,accepted⟩ := WordFieldReader.ready_total_execution input slot high width
    ready.status (ready.workspace 1 (by decide)) (ready.workspace 2 (by decide)) ready.savedWidth
    (ready.workspace 10 (by decide)) (ready.workspace 11 (by decide)) (ready.workspace 12 (by decide))
    (ready.workspace 20 (by decide)) empty
  change ticks ≤ 16*(mass input)^2+30*mass input+26 at timeBound
  refine ⟨ticks,peak,_,trace,?_,accepted,?_⟩
  · unfold cost
    omega
  · intro words suffix decoded
    simp only [WordFieldReader.result,decoded]

theorem field_total (input : Port → List Bool) (field : Field) (fields : List Field)
    (ready : Ready input width registers (field :: fields)) :
    ∃ ticks peak output, Execution field.program ⟨some field.program.main,input⟩ ⟨none,output⟩ ticks peak ∧
      ticks ≤ cost (mass input) ∧ Option.isNone ((output none).head?)=(field.read width registers (input (some 0))).isSome ∧
      (∀ words suffix, field.read width registers (input (some 0))=some (words,suffix) →
        output=WordFieldReader.packet input field.slot width words suffix) := by
  have empty := ready.targets field (by simp)
  cases field with
  | registers =>
    obtain ⟨ticks,peak,output,trace,timeBound,spaceBound,accepted,observed⟩ := CheckedWordField.register_total input width registers
      ready.status (ready.workspace 1 (by decide)) (ready.workspace 2 (by decide)) ready.savedWidth ready.savedRegisters
      (ready.workspace 10 (by decide)) (ready.workspace 11 (by decide)) (ready.workspace 12 (by decide))
      (ready.workspace 16 (by decide)) (ready.workspace 17 (by decide)) (ready.workspace 20 (by decide)) empty
    exact ⟨ticks,peak,output,trace,timeBound,accepted,observed⟩
  | control =>
    obtain ⟨ticks,peak,output,trace,timeBound,spaceBound,accepted,observed⟩ := CheckedWordField.pc_total input width
      ready.status (ready.workspace 1 (by decide)) (ready.workspace 2 (by decide)) ready.savedWidth
      (ready.workspace 10 (by decide)) (ready.workspace 11 (by decide)) (ready.workspace 12 (by decide))
      (ready.workspace 20 (by decide)) empty
    exact ⟨ticks,peak,output,trace,timeBound,accepted,observed⟩
  | heap => exact normal_total input 22 (by decide) ready empty
  | stack => exact normal_total input 23 (by decide) ready empty
  | output => exact normal_total input 24 (by decide) ready empty

theorem tail_sound {source : List Bool} {halt : Bool} (decoded : StateShape.decodeTail source=some halt) : source=[halt] := by
  cases source with
  | nil => simp [StateShape.decodeTail] at decoded
  | cons bit rest =>
    cases rest with
    | nil => exact congrArg (fun bit => [bit]) (show bit=halt by simpa only [StateShape.decodeTail,Option.some.injEq] using decoded)
    | cons extra rest => simp [StateShape.decodeTail] at decoded

theorem read_nil_sound {width registers : Nat} {source : List Bool} {values : List (List (Controller.Cost.Word width))} {halt : Bool}
    (decoded : read width registers [] source=some (values,halt)) : values=[] ∧ source=[halt] := by
  cases parsed : StateShape.decodeTail source with
  | none => simp [read,parsed] at decoded
  | some bit =>
    simp only [read,parsed,Option.map_some,Option.some.injEq,Prod.mk.injEq] at decoded
    rcases decoded with ⟨rfl,rfl⟩
    exact ⟨rfl,tail_sound parsed⟩

theorem time_join (first tail size count : Nat) (one : first ≤ cost size) (rest : tail ≤ count*(cost size+1)+5) :
    first+tail ≤ (count+1)*(cost size+1)+5 := by
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem time_reject (first size count : Nat) (one : first ≤ cost size) :
    first+1 ≤ (count+1)*(cost size+1)+5 := by
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem total_execution (width registers : Nat) (fields : List Field) (input : Port → List Bool)
    (ready : Ready input width registers fields) (distinct : (fields.map Field.slot).Nodup) :
    ∃ ticks peak output, Execution (program fields) ⟨some (program fields).main,input⟩ ⟨none,output⟩ ticks peak ∧
      ticks ≤ fields.length*(cost (mass input)+1)+5 ∧
      Option.isNone ((output none).head?)=(read width registers fields (input (some 0))).isSome ∧
      (∀ values halt, read width registers fields (input (some 0))=some (values,halt) → output=store input width fields values halt) := by
  induction fields generalizing input with
  | nil =>
    obtain ⟨ticks,peak,trace,timeBound,accepted⟩ := StateShape.tail_ready input ready.status ready.haltEmpty
    refine ⟨ticks,peak,_,trace,?_,?_,?_⟩
    · simpa only [List.length_nil,Nat.zero_mul,Nat.zero_add] using timeBound
    · simpa only [read,Option.isSome_map] using accepted
    · intro values halt decoded
      obtain ⟨rfl,shape⟩ := read_nil_sound decoded
      simp only [shape,StateShape.tailResult,ite_true,store,fieldsBank]
  | cons field fields ih =>
    obtain ⟨ticks,peak,middle,first,timeBound,accepted,observed⟩ := field_total input field fields ready
    cases parsed : field.read width registers (input (some 0)) with
    | none =>
      have rejected : Option.isNone ((middle none).head?)=false := by simpa only [parsed,Option.isSome_none] using accepted
      have trace := GuardedLink.failure (program fields) none Option.isNone first rejected
      refine ⟨ticks+1,peak,middle,trace,?_,?_,?_⟩
      · exact time_reject ticks (mass input) fields.length timeBound
      · simpa [read,parsed] using rejected
      · intro values halt impossible
        simp [read,parsed] at impossible
    | some pair =>
      rcases pair with ⟨words,suffix⟩
      have endpoint := observed words suffix parsed
      rw [endpoint] at first
      have nextReady := ready.packet input field fields distinct words suffix
      have conserved := packet_mass input field fields ready words suffix parsed
      have nextDistinct : (fields.map Field.slot).Nodup := (List.nodup_cons.mp distinct).2
      obtain ⟨tailTicks,tailPeak,output,tail,tailTime,tailAccepted,tailObserved⟩ := ih
        (WordFieldReader.packet input field.slot width words suffix) nextReady nextDistinct
      rw [conserved] at tailTime
      have source : WordFieldReader.packet input field.slot width words suffix (some 0)=suffix := by
        simp [WordFieldReader.packet_at input field.slot field.slot_high]
      rw [source] at tailAccepted tailObserved
      have trace := GuardedLink.success none Option.isNone first tail (by simp [WordFieldReader.packet_at input field.slot field.slot_high])
      refine ⟨ticks+tailTicks,max peak tailPeak,output,trace,?_,?_,?_⟩
      · exact time_join ticks tailTicks (mass input) fields.length timeBound tailTime
      · rw [tailAccepted]
        simp only [read,parsed,Bind.bind,Option.bind]
        cases read width registers fields suffix <;> rfl
      · intro values halt decoded
        cases restRead : read width registers fields suffix with
        | none => simp [read,parsed,restRead] at decoded
        | some pair =>
          rcases pair with ⟨rest,bit⟩
          simp only [read,parsed,restRead,Bind.bind,Option.bind,Option.pure_def,Option.some.injEq,Prod.mk.injEq] at decoded
          rcases decoded with ⟨rfl,rfl⟩
          exact (tailObserved rest _ restRead).trans (store_packet input field fields ready words suffix rest _)

def fields : List Field := [.registers,.heap,.stack,.output,.control]
def stateProgram := program fields

theorem state_total (width registers : Nat) (input : Port → List Bool) (ready : Ready input width registers fields) :
    ∃ ticks peak output, Execution stateProgram ⟨some stateProgram.main,input⟩ ⟨none,output⟩ ticks peak ∧
      ticks ≤ 80*(mass input)^2+200*mass input+210 ∧ peak ≤ 80*(mass input)^2+201*mass input+210 ∧
      Option.isNone ((output none).head?)=(read width registers fields (input (some 0))).isSome ∧
      (∀ values halt, read width registers fields (input (some 0))=some (values,halt) → output=store input width fields values halt) := by
  obtain ⟨ticks,peak,output,trace,timeBound,accepted,observed⟩ := total_execution width registers fields input ready (by decide)
  have identity : fields.length*(cost (mass input)+1)+5=80*(mass input)^2+200*mass input+210 := by simp only [fields,List.length_cons,List.length_nil,cost]; ring
  rw [identity] at timeBound
  have space := trace.peak_le
  change peak ≤ mass input+ticks at space
  exact ⟨ticks,peak,output,trace,timeBound,by omega,accepted,observed⟩

theorem label_card_nil : Fintype.card (Label [])=7 := by
  have same : Fintype.card (Label [])=Fintype.card (Fin 7) :=
    @Fintype.card_congr (Label []) (Fin 7) _ _ (Equiv.refl _)
  exact same.trans (Fintype.card_fin 7)

theorem label_card_cons (field : Field) (fields : List Field) :
    Fintype.card (Label (field :: fields))=Fintype.card field.Label+(Fintype.card (Label fields)+1) := by
  have same : Fintype.card (Label (field :: fields))=Fintype.card (field.Label ⊕ Option (Label fields)) :=
    @Fintype.card_congr (Label (field :: fields)) (field.Label ⊕ Option (Label fields)) _ _ (Equiv.refl _)
  exact same.trans (by simp only [Fintype.card_sum,Fintype.card_option])

def fieldLabels : Field → Nat
  | .registers => 113
  | .control => 91
  | _ => 85

theorem field_card (field : Field) : Fintype.card field.Label=fieldLabels field := by
  cases field with
  | registers =>
    have same : Fintype.card (Field.Label .registers)=Fintype.card (LabelsOf (CheckedWordField.registerProgram)) :=
      @Fintype.card_congr (Field.Label .registers) (LabelsOf (CheckedWordField.registerProgram)) _ _ (Equiv.refl _)
    exact same.trans (by simp only [LabelsOf,fieldLabels,Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd])
  | heap =>
    have same : Fintype.card (Field.Label .heap)=Fintype.card (LabelsOf (WordFieldReader.program 22)) :=
      @Fintype.card_congr (Field.Label .heap) (LabelsOf (WordFieldReader.program 22)) _ _ (Equiv.refl _)
    exact same.trans (by simp only [LabelsOf,fieldLabels,Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd])
  | stack =>
    have same : Fintype.card (Field.Label .stack)=Fintype.card (LabelsOf (WordFieldReader.program 23)) :=
      @Fintype.card_congr (Field.Label .stack) (LabelsOf (WordFieldReader.program 23)) _ _ (Equiv.refl _)
    exact same.trans (by simp only [LabelsOf,fieldLabels,Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd])
  | output =>
    have same : Fintype.card (Field.Label .output)=Fintype.card (LabelsOf (WordFieldReader.program 24)) :=
      @Fintype.card_congr (Field.Label .output) (LabelsOf (WordFieldReader.program 24)) _ _ (Equiv.refl _)
    exact same.trans (by simp only [LabelsOf,fieldLabels,Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd])
  | control =>
    have same : Fintype.card (Field.Label .control)=Fintype.card (LabelsOf (CheckedWordField.pcProgram)) :=
      @Fintype.card_congr (Field.Label .control) (LabelsOf (CheckedWordField.pcProgram)) _ _ (Equiv.refl _)
    exact same.trans (by simp only [LabelsOf,fieldLabels,Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd])

theorem canonical_card : Fintype.card (Label fields)=471 := by
  have c₀ := label_card_nil
  have c₁ := (label_card_cons .control []).trans
    (congrArg₂ (fun x y : Nat => x+(y+1)) (field_card .control) c₀)
  have c₂ := (label_card_cons .output [.control]).trans
    (congrArg₂ (fun x y : Nat => x+(y+1)) (field_card .output) c₁)
  have c₃ := (label_card_cons .stack [.output,.control]).trans
    (congrArg₂ (fun x y : Nat => x+(y+1)) (field_card .stack) c₂)
  have c₄ := (label_card_cons .heap [.stack,.output,.control]).trans
    (congrArg₂ (fun x y : Nat => x+(y+1)) (field_card .heap) c₃)
  exact (label_card_cons .registers [.heap,.stack,.output,.control]).trans
    (congrArg₂ (fun x y : Nat => x+(y+1)) (field_card .registers) c₄)

theorem resident : (∑ label, statementSize (tmStatement (stateProgram.code label))) ≤ 4239 := by
  have bound := finiteTM_resident (K := Fin 31) (Q := Label fields) stateProgram
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.StateReader
