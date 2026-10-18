module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.Model
public import Mathlib.Computability.Encoding
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Finite machine words have an exact-width binary representation. A unary
count delimiter frames lists of those words, with linear storage overhead.
These are storage encodings over the fixed alphabet `Bool`. -/
namespace Controller.Complexity.Encoding
open Controller.Cost

def bits : Nat → Nat → List Bool
  | 0, _ => []
  | width+1, value => decide (value%2=1) :: bits width (value/2)

def value : List Bool → Nat
  | [] => 0
  | bit :: rest => 2*value rest+(if bit then 1 else 0)

@[simp] theorem bits_length (width number : Nat) : (bits width number).length = width := by
  induction width generalizing number with
  | zero => rfl
  | succ width ih => simp only [bits,List.length_cons,ih]

theorem value_lt (digits : List Bool) : value digits < 2^digits.length := by
  induction digits with
  | nil => decide
  | cons bit rest ih =>
    simp only [value,List.length_cons,Nat.pow_succ]
    cases bit <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

theorem value_bits (width number : Nat) (bound : number<2^width) : value (bits width number) = number := by
  induction width generalizing number with
  | zero =>
    have zero : number=0 := by simpa only [Nat.pow_zero,Nat.lt_one_iff] using bound
    subst number
    rfl
  | succ width ih =>
    have half : number/2<2^width := by rw [Nat.pow_succ] at bound; omega
    simp only [bits,value,ih _ half]
    split <;> rename_i parity <;> simp only [decide_eq_true_eq] at parity <;> omega

def decodeWord (width : Nat) (digits : List Bool) : Option (Word width) :=
  if same : digits.length=width then some ⟨value digits,by rw [← same]; exact value_lt digits⟩ else none

def wordEncoding (width : Nat) : Computability.Encoding (Word width) Bool where
  encode word := bits width word.val
  decode := decodeWord width
  decode_encode word := by
    simp only [decodeWord,bits_length,dite_eq_left True.intro]
    apply congrArg some
    apply Fin.ext
    exact value_bits width word.val word.isLt

@[simp] theorem word_length (word : Word width) : ((wordEncoding width).encode word).length = width :=
  bits_length width word.val

theorem decodeWord_wrong_length (digits : List Bool) (wrong : digits.length≠width) :
    decodeWord width digits = none := by simp only [decodeWord,dite_eq_right wrong]

def wordList (width : Nat) (words : List (Word width)) : List Bool :=
  words.flatMap (wordEncoding width).encode

@[simp] theorem wordList_length (words : List (Word width)) : (wordList width words).length = width*words.length := by
  induction words with
  | nil => simp [wordList]
  | cons word rest ih =>
    simp only [wordList,List.flatMap_cons,List.length_append,word_length,List.length_cons,Nat.mul_add,Nat.mul_one] at *
    omega

def readWords (width : Nat) : Nat → List Bool → Option (List (Word width) × List Bool)
  | 0, input => some ([],input)
  | count+1, input => do
    let word ← decodeWord width (input.take width)
    let (words,rest) ← readWords width count (input.drop width)
    pure (word :: words,rest)

theorem readWords_encoded (words : List (Word width)) (suffix : List Bool) :
    readWords width words.length (wordList width words ++ suffix) = some (words,suffix) := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    have first := (wordEncoding width).decode_encode word
    change decodeWord width (bits width word.val) = some word at first
    simp only [wordList,List.flatMap_cons,List.length_cons,List.append_assoc,readWords]
    rw [List.take_append_of_le_length (by simp),List.take_of_length_le (by simp),
      List.drop_append_of_le_length (by simp),List.drop_of_length_le (by simp)]
    change (do
      let head ← decodeWord width (bits width word.val)
      let pair ← readWords width rest.length (wordList width rest ++ suffix)
      pure (head :: pair.1,pair.2)) = some (word :: rest,suffix)
    rw [first]
    simp only [Bind.bind,Option.bind]
    rw [ih]
    rfl

def frameCount (count : Nat) (payload : List Bool) : List Bool :=
  List.replicate count true ++ false :: payload

def readCount : List Bool → Option (Nat × List Bool)
  | [] => none
  | false :: rest => some (0,rest)
  | true :: rest => (readCount rest).map fun pair => (pair.1+1,pair.2)

@[simp] theorem readCount_frame (count : Nat) (payload : List Bool) :
    readCount (frameCount count payload) = some (count,payload) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simpa only [frameCount,List.replicate_succ,List.cons_append,readCount,Option.map_some] using
      congrArg (Option.map fun pair => (pair.1+1,pair.2)) ih

def encodeWords (width : Nat) (words : List (Word width)) : List Bool :=
  frameCount words.length (wordList width words)

def decodeWords (width : Nat) (input : List Bool) : Option (List (Word width)) := do
  let (count,payload) ← readCount input
  let (words,rest) ← readWords width count payload
  if rest=[] then some words else none

def wordsEncoding (width : Nat) : Computability.Encoding (List (Word width)) Bool where
  encode := encodeWords width
  decode := decodeWords width
  decode_encode words := by
    simp only [encodeWords,decodeWords,readCount_frame,Bind.bind,Option.bind]
    have read := readWords_encoded words ([] : List Bool)
    simp only [List.append_nil] at read
    rw [read]
    rfl

theorem encodeWords_length (words : List (Word width)) :
    (encodeWords width words).length = (width+1)*words.length+1 := by
  simp only [encodeWords,frameCount,List.length_append,List.length_replicate,List.length_cons,wordList_length,
    Nat.add_mul,Nat.one_mul]
  omega

@[simp] theorem encodeWords_nil : encodeWords width [] = [false] := rfl
@[simp] theorem decodeWords_nil : decodeWords width [] = none := rfl

def readFramedWords (width : Nat) (input : List Bool) : Option (List (Word width) × List Bool) := do
  let (count,payload) ← readCount input
  readWords width count payload

theorem readFramedWords_encoded (words : List (Word width)) (suffix : List Bool) :
    readFramedWords width (encodeWords width words ++ suffix) = some (words,suffix) := by
  have frame : encodeWords width words ++ suffix = frameCount words.length (wordList width words ++ suffix) := by
    simp only [encodeWords,frameCount,List.append_assoc,List.cons_append]
  rw [frame]
  simp only [readFramedWords,readCount_frame,Bind.bind,Option.bind]
  exact readWords_encoded words suffix

end Controller.Complexity.Encoding
