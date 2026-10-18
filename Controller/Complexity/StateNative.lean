module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.StateReader

@[expose] public section

/-! The executed state reader agrees with the native state decoder. Actual
persistent banks retain the exact original state bytes, so successful native
State observation includes every register, heap/stack/output word, PC and flag. -/
namespace Controller.Complexity.StateNative
open StackMachine WordReader StateReader
open CheckedWordField (mass)
open scoped BigOperators

def bytes (values : List (List (Controller.Cost.Word width))) (halt : Bool) : List Bool :=
  values.flatMap (Encoding.encodeWords width)++[halt]

theorem read_inverse (width registers : Nat) (fields : List Field) (source : List Bool)
    (values : List (List (Controller.Cost.Word width))) (halt : Bool)
    (decoded : StateReader.read width registers fields source=some (values,halt)) :
    source=bytes values halt ∧ values.length=fields.length := by
  induction fields generalizing source values with
  | nil =>
    obtain ⟨rfl,shape⟩ := read_nil_sound decoded
    exact ⟨shape,rfl⟩
  | cons field fields ih =>
    cases first : field.read width registers source with
    | none => simp [StateReader.read,first] at decoded
    | some pair =>
      rcases pair with ⟨words,suffix⟩
      cases rest : StateReader.read width registers fields suffix with
      | none => simp [StateReader.read,first,rest] at decoded
      | some pair =>
        rcases pair with ⟨tail,bit⟩
        simp only [StateReader.read,first,rest,Bind.bind,Option.bind,Option.pure_def,Option.some.injEq,Prod.mk.injEq] at decoded
        rcases decoded with ⟨rfl,rfl⟩
        obtain ⟨shape,length⟩ := ih suffix tail rest
        refine ⟨?_,by simp only [List.length_cons,length]⟩
        rw [field_read_sound field width registers source words suffix first,shape]
        simp only [bytes,List.flatMap_cons,List.append_assoc]


def nativeTail (width registers : Nat) (values heap stack output control : List (Controller.Cost.Word width))
    (rest : List Bool) : Option (Controller.Cost.State width registers) :=
  match control,rest with
  | [pc],[halted] =>
    if same : values.length=registers then
      some {
        reg := fun i => values[i.val]'(by rw [same]; exact i.isLt)
        heap := heap.toArray
        stack := stack
        output := output
        pc := pc
        halted := halted }
    else none
  | _,_ => none

def afterRegisters (width registers : Nat) (values : List (Controller.Cost.Word width)) (source : List Bool) := do
  let (heap,two) ← Encoding.readFramedWords width source
  let (stack,three) ← Encoding.readFramedWords width two
  let (output,four) ← Encoding.readFramedWords width three
  let (control,rest) ← Encoding.readFramedWords width four
  nativeTail width registers values heap stack output control rest

theorem bind_accept_flag (source : Option A) (left : A → Option B) (right : A → Option C) (flag : Bool)
    (same : ∀ a, ((left a).isSome && flag)=(right a).isSome) :
    ((source.bind left).isSome && flag)=(source.bind right).isSome := by
  cases source with
  | none => rfl
  | some a => exact same a

theorem bind_accept (source : Option A) (left : A → Option B) (right : A → Option C)
    (same : ∀ a, (left a).isSome=(right a).isSome) :
    (source.bind left).isSome=(source.bind right).isSome := by
  cases source with
  | none => rfl
  | some a => exact same a

theorem prepend_accept (words : List (Controller.Cost.Word width)) (rest : Option (List (List (Controller.Cost.Word width)) × Bool)) :
    (rest.bind fun (values,halt) => some (words :: values,halt)).isSome=rest.isSome := by cases rest <;> rfl

theorem control_value_accept (width registers : Nat) (values heap stack output control : List (Controller.Cost.Word width)) (rest : List Bool) :
    (((if decide (control.length=1) then some (control,rest) else none).bind fun (words,suffix) =>
      (StateReader.read width registers [] suffix).bind fun (tail,halt) => some (words :: tail,halt)).isSome && decide (values.length=registers))=
      (nativeTail width registers values heap stack output control rest).isSome := by
  cases control with
  | nil => simp [nativeTail]
  | cons pc control =>
    cases control with
    | cons extra control => simp [nativeTail]
    | nil =>
      cases rest with
      | nil => simp [StateReader.read,StateShape.decodeTail,nativeTail]
      | cons bit rest =>
        cases rest with
        | nil => by_cases same : values.length=registers <;> simp [StateReader.read,StateShape.decodeTail,nativeTail,same]
        | cons extra rest => simp [StateReader.read,StateShape.decodeTail,nativeTail]

theorem control_accept (width registers : Nat) (values heap stack output : List (Controller.Cost.Word width)) (source : List Bool) :
    ((StateReader.read width registers [.control] source).isSome && decide (values.length=registers))=
      ((Encoding.readFramedWords width source).bind fun (control,rest) => nativeTail width registers values heap stack output control rest).isSome := by
  simp only [StateReader.read,Field.read,CheckedWordField.readField,Bind.bind,Option.bind_assoc]
  apply bind_accept_flag
  rintro ⟨control,rest⟩
  exact control_value_accept width registers values heap stack output control rest

theorem after_registers_accept (width registers : Nat) (values : List (Controller.Cost.Word width)) (source : List Bool) :
    ((StateReader.read width registers [.heap,.stack,.output,.control] source).isSome && decide (values.length=registers))=
      (afterRegisters width registers values source).isSome := by
  change (((Encoding.readFramedWords width source).bind fun (heap,two) =>
    (StateReader.read width registers [.stack,.output,.control] two).bind fun (tail,halt) => some (heap :: tail,halt)).isSome && decide (values.length=registers))=_
  unfold afterRegisters
  apply bind_accept_flag
  rintro ⟨heap,two⟩
  rw [prepend_accept]
  change (((Encoding.readFramedWords width two).bind fun (stack,three) =>
    (StateReader.read width registers [.output,.control] three).bind fun (tail,halt) => some (stack :: tail,halt)).isSome && decide (values.length=registers))=_
  apply bind_accept_flag
  rintro ⟨stack,three⟩
  rw [prepend_accept]
  change (((Encoding.readFramedWords width three).bind fun (output,four) =>
    (StateReader.read width registers [.control] four).bind fun (tail,halt) => some (output :: tail,halt)).isSome && decide (values.length=registers))=_
  apply bind_accept_flag
  rintro ⟨output,four⟩
  rw [prepend_accept]
  exact control_accept width registers values heap stack output four

theorem accepts_native (width registers : Nat) (source : List Bool) :
    (StateReader.read width registers StateReader.fields source).isSome=(MachineBridge.decodeState width registers source).isSome := by
  change ((CheckedWordField.readField (fun count => decide (count=registers)) width source).bind fun (values,rest) =>
    (StateReader.read width registers [.heap,.stack,.output,.control] rest).bind fun (tail,halt) => some (values :: tail,halt)).isSome=
      ((Encoding.readFramedWords width source).bind fun (values,rest) => afterRegisters width registers values rest).isSome
  simp only [CheckedWordField.readField,Bind.bind,Option.bind_assoc]
  apply bind_accept
  rintro ⟨values,rest⟩
  by_cases same : values.length=registers <;>
    simpa [same,prepend_accept] using after_registers_accept width registers values rest

def storedBytes (input : Port → List Bool) : List Bool :=
  input (some 21)++(input (some 22)++(input (some 23)++(input (some 24)++(input (some 25)++input (some 26)))))

def observe (width registers : Nat) (input : Port → List Bool) : Option (Controller.Cost.State width registers) :=
  MachineBridge.decodeState width registers (storedBytes input)

theorem fieldsBank_other (input : Port → List Bool) (width : Nat) (fields : List Field)
    (values : List (List (Controller.Cost.Word width))) (address : Port)
    (outside : ∀ field ∈ fields, address ≠ some field.slot) :
    fieldsBank input width fields values address=input address := by
  induction fields generalizing input values with
  | nil => rfl
  | cons field fields ih =>
    cases values with
    | nil => rfl
    | cons words values =>
      rw [fieldsBank,ih _ values (by intro next member; exact outside next (by simp [member]))]
      simp [outside field (by simp)]

theorem store_other (input : Port → List Bool) (width : Nat) (fields : List Field)
    (values : List (List (Controller.Cost.Word width))) (halt : Bool) (address : Port)
    (notStatus : address ≠ none) (notSource : address ≠ some 0) (notHalt : address ≠ some 26)
    (outside : ∀ field ∈ fields, address ≠ some field.slot) :
    store input width fields values halt address=input address := by
  simp only [store,StateShape.tail_at,ite_eq_right notStatus,ite_eq_right notSource,ite_eq_right notHalt]
  exact fieldsBank_other input width fields values address outside

theorem store_status (input : Port → List Bool) (width : Nat) (fields : List Field)
    (values : List (List (Controller.Cost.Word width))) (halt : Bool) :
    store input width fields values halt none=[] := by simp [store,StateShape.tail_at]

theorem store_eof (input : Port → List Bool) (width : Nat) (fields : List Field)
    (values : List (List (Controller.Cost.Word width))) (halt : Bool) :
    store input width fields values halt (some 0)=[] := by simp [store,StateShape.tail_at]

theorem stored_bytes (input : Port → List Bool) (values : List (List (Controller.Cost.Word width))) (halt : Bool)
    (length : values.length=5) : storedBytes (store input width StateReader.fields values halt)=bytes values halt := by
  rcases values with _ | ⟨a,values⟩ <;> simp only [List.length_nil,List.length_cons] at length
  · omega
  rcases values with _ | ⟨b,values⟩ <;> simp only [List.length_nil,List.length_cons] at length
  · omega
  rcases values with _ | ⟨c,values⟩ <;> simp only [List.length_nil,List.length_cons] at length
  · omega
  rcases values with _ | ⟨d,values⟩ <;> simp only [List.length_nil,List.length_cons] at length
  · omega
  rcases values with _ | ⟨e,values⟩ <;> simp only [List.length_nil,List.length_cons] at length
  · omega
  have empty : values=[] := List.length_eq_zero_iff.mp (by omega)
  subst values
  simp [storedBytes,store,fieldsBank,StateReader.fields,Field.slot,StateShape.tail_at,bytes,List.append_assoc]

theorem stored_observation (width registers : Nat) (input : Port → List Bool)
    (values : List (List (Controller.Cost.Word width))) (halt : Bool)
    (decoded : StateReader.read width registers StateReader.fields (input (some 0))=some (values,halt)) :
    observe width registers (store input width StateReader.fields values halt)=MachineBridge.decodeState width registers (input (some 0)) := by
  obtain ⟨shape,length⟩ := read_inverse width registers StateReader.fields (input (some 0)) values halt decoded
  have five : values.length=5 := by simpa only [StateReader.fields,List.length_cons,List.length_nil] using length
  rw [observe,stored_bytes input values halt five,← shape]

theorem total_decodes (width registers : Nat) (input : Port → List Bool)
    (ready : Ready input width registers StateReader.fields) :
    ∃ ticks peak output, Execution stateProgram ⟨some stateProgram.main,input⟩ ⟨none,output⟩ ticks peak ∧
      ticks ≤ 80*(mass input)^2+200*mass input+210 ∧ peak ≤ 80*(mass input)^2+201*mass input+210 ∧
      Option.isNone ((output none).head?)=(MachineBridge.decodeState width registers (input (some 0))).isSome ∧
      (∀ state, MachineBridge.decodeState width registers (input (some 0))=some state → observe width registers output=some state) := by
  obtain ⟨ticks,peak,output,trace,timeBound,spaceBound,accepted,observed⟩ := state_total width registers input ready
  rw [accepts_native] at accepted
  refine ⟨ticks,peak,output,trace,timeBound,spaceBound,accepted,?_⟩
  intro state decoded
  have existsParts : (StateReader.read width registers StateReader.fields (input (some 0))).isSome=true := by
    rw [accepts_native,decoded]
    rfl
  obtain ⟨⟨values,halt⟩,parsed⟩ := Option.isSome_iff_exists.mp existsParts
  rw [observed values halt parsed,stored_observation width registers input values halt parsed,decoded]

theorem encoded_total (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (ready : Ready input width registers StateReader.fields) (source : input (some 0)=MachineBridge.encodeState state) :
    ∃ ticks peak output, Execution stateProgram ⟨some stateProgram.main,input⟩ ⟨none,output⟩ ticks peak ∧
      ticks ≤ 80*(mass input)^2+200*mass input+210 ∧ peak ≤ 80*(mass input)^2+201*mass input+210 ∧
      output none=[] ∧ observe width registers output=some state := by
  obtain ⟨ticks,peak,output,trace,timeBound,spaceBound,accepted,observed⟩ := total_decodes width registers input ready
  have decoded : MachineBridge.decodeState width registers (input (some 0))=some state := by
    rw [source,MachineBridge.decode_encode]
  have flag : Option.isNone ((output none).head?)=true := by simpa only [decoded,Option.isSome_some] using accepted
  have clean : output none=[] := by
    cases shape : output none with
    | nil => rfl
    | cons bit rest => simp [shape] at flag
  exact ⟨ticks,peak,output,trace,timeBound,spaceBound,clean,observed state decoded⟩

end Controller.Complexity.StateNative
