module
public meta import Lean.Elab.Command
public meta import Lean.Meta.Match.Match
meta import all Lean.Meta.Match.Match
public meta import Lean.Meta.Tactic.AuxLemma


public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Computability.Encoding
public import Mathlib.Computability.Partrec
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Size
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/- Preserve source-module names and module-local elaboration caches when
   flattening definitions. Every declaration is still checked by Lean. -/
open Lean Elab Command in
elab "source_context " source:str : command => do
  let root := (← getOptions).get `sourceContextRoot ""
  if root.isEmpty then
    let original := (← getEnv).mainModule
    modifyScope fun scope => { scope with opts := scope.opts.set `sourceContextRoot original.toString }
  modifyEnv fun env =>
    let env := env.setMainModule source.getString.toName
    let env := Meta.auxLemmasExt.setState env {}
    (private_decl% Lean.Meta.Match.matcherExt).setState env {}
open Lean Elab Command in
elab "end_source_context" : command => do
  let root := (← getOptions).get `sourceContextRoot ""
  if root.isEmpty then throwError "missing original Challenge module"
  modifyEnv (·.setMainModule root.toName)

@[expose] public section

/-!
# Resource-respecting encoded simulation and reduction composition

The grammar, state transitions, resource measures and mathematical predicates
are explicit. Definition holes identify only implementation witnesses; the
selected universal theorems constrain their executions or returned results.
The selected statements retain the exact assumptions of the proof library.
-/

/- Definitions from Controller.Cost.Model. -/
source_context "Controller.Cost.Model"
namespace Controller.Cost
abbrev Word (width : Nat) := Fin (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat)) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) width)
def word (width value : Nat) : Word width :=
  ⟨value % ((@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 width)), Nat.mod_lt _ (Nat.two_pow_pos width)⟩
structure State (width registers : Nat) where
  reg : Fin registers → Word width
  heap : Array (Word width)
  stack : List (Word width)
  output : List (Word width)
  pc : Word width
  halted : Bool
def State.liveWords (s : State width registers) : Nat :=
  registers + s.heap.size + s.stack.length + s.output.length + 1
inductive Instruction (width registers : Nat) where
  | constant (dst : Fin registers) (value : Word width)
  | copy (dst src : Fin registers)
  | add (dst left right : Fin registers)
  | xor (dst left right : Fin registers)
  | load (dst address : Fin registers)
  | store (address src : Fin registers)
  | allocate (src : Fin registers)
  | release
  | push (src : Fin registers)
  | pop (dst : Fin registers)
  | emit (src : Fin registers)
  | branchZero (src : Fin registers) (target : Word width)
  | halt
def State.put (s : State width registers) (dst : Fin registers)
    (value : Word width) : State width registers :=
  { s with reg := fun i => if i = dst then value else s.reg i }
def State.advance (s : State width registers) : State width registers :=
  { s with pc := word width (s.pc.val + 1) }
/-- Invalid reads, writes, stack pops and releases have no transition.
A halted state also has no further transition. -/
def step (instruction : Instruction width registers) (s : State width registers) :
    Option (State width registers) :=
  if s.halted then none else
  let next := s.advance
  match instruction with
  | .constant dst value => some (next.put dst value)
  | .copy dst src => some (next.put dst (s.reg src))
  | .add dst left right => some (next.put dst (word width ((s.reg left).val + (s.reg right).val)))
  | .xor dst left right => some (next.put dst (word width (Nat.xor (s.reg left).val (s.reg right).val)))
  | .load dst address =>
      if h : (s.reg address).val < s.heap.size then
        some (next.put dst s.heap[(s.reg address).val]) else none
  | .store address src =>
      if h : (s.reg address).val < s.heap.size then
        some { next with heap := s.heap.set (s.reg address).val (s.reg src) } else none
  | .allocate src =>
      if s.heap.size < (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 width) then some { next with heap := s.heap.push (s.reg src) }
      else none
  | .release => if s.heap.isEmpty then none else some { next with heap := s.heap.pop }
  | .push src => some { next with stack := s.reg src :: s.stack }
  | .pop dst => match s.stack with
      | [] => none
      | value :: rest => some { next.put dst value with stack := rest }
  | .emit src => some { next with output := s.reg src :: s.output }
  | .branchZero src target =>
      some (if (s.reg src).val = 0 then { next with pc := target } else next)
  | .halt => some { next with halted := true }
abbrev Program (width registers : Nat) := Array (Instruction width registers)
def programStep (p : Program width registers) (s : State width registers) :
    Option (State width registers) := do
  let instruction ← p[s.pc.val]?
  step instruction s
/-- A proof trace consists of genuine successive machine transitions. -/
inductive Execution (p : Program width registers) :
    State width registers → State width registers → Nat → Nat → Prop where
  | refl (s) : Execution p s s 0 s.liveWords
  | cons {s middle final ticks peak}
      (transition : programStep p s = some middle)
      (rest : Execution p middle final ticks peak) :
      Execution p s final (ticks + 1) (max s.liveWords peak)
end Controller.Cost

/- Definitions from Controller.Complexity.Encoding. -/
source_context "Controller.Complexity.Encoding"
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
def wordList (width : Nat) (words : List (Word width)) : List Bool :=
  words.flatMap (wordEncoding width).encode
def readWords (width : Nat) : Nat → List Bool → Option (List (Word width) × List Bool)
  | 0, input => some ([],input)
  | count+1, input => do
    let word ← decodeWord width (input.take width)
    let (words,rest) ← readWords width count (input.drop width)
    pure (word :: words,rest)
def frameCount (count : Nat) (payload : List Bool) : List Bool :=
  List.replicate count true ++ false :: payload
def readCount : List Bool → Option (Nat × List Bool)
  | [] => none
  | false :: rest => some (0,rest)
  | true :: rest => (readCount rest).map fun pair => (pair.1+1,pair.2)
def encodeWords (width : Nat) (words : List (Word width)) : List Bool :=
  frameCount words.length (wordList width words)
def decodeWords (width : Nat) (input : List Bool) : Option (List (Word width)) := do
  let (count,payload) ← readCount input
  let (words,rest) ← readWords width count payload
  if rest=[] then some words else none
def readFramedWords (width : Nat) (input : List Bool) : Option (List (Word width) × List Bool) := do
  let (count,payload) ← readCount input
  readWords width count payload
end Controller.Complexity.Encoding

/- Definitions from Controller.Complexity.MachineBridge. -/
source_context "Controller.Complexity.MachineBridge"
namespace Controller.Complexity.MachineBridge
open Controller.Cost Controller.Complexity.Encoding
def encodeState (state : State width registers) : List Bool :=
  encodeWords width (List.ofFn state.reg) ++
    (encodeWords width state.heap.toList ++
    (encodeWords width state.stack ++
    (encodeWords width state.output ++
    (encodeWords width [state.pc] ++ [state.halted]))))
def decodeState (width registers : Nat) (input : List Bool) : Option (State width registers) := do
  let (values,rest) ← readFramedWords width input
  let (heap,rest) ← readFramedWords width rest
  let (stack,rest) ← readFramedWords width rest
  let (output,rest) ← readFramedWords width rest
  let (control,rest) ← readFramedWords width rest
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
end Controller.Complexity.MachineBridge
namespace Controller.Complexity.InstructionCodec
open Controller.Cost Controller.Complexity.Encoding
def registerWord (bound : registers ≤ 2^width) (register : Fin registers) : Word width :=
  ⟨register.val, register.isLt.trans_le bound⟩
def readRegister (value : Word width) : Option (Fin registers) :=
  if h : value.val < registers then some ⟨value.val, h⟩ else none
/-- Opcode and ordered operands; unused operand slots are omitted. -/
def fields (bound : registers ≤ 2^width) : Instruction width registers → Nat × List (Word width)
  | .constant dst value => (0, [registerWord bound dst, value])
  | .copy dst src => (1, [registerWord bound dst, registerWord bound src])
  | .add dst left right => (2, [registerWord bound dst, registerWord bound left, registerWord bound right])
  | .xor dst left right => (3, [registerWord bound dst, registerWord bound left, registerWord bound right])
  | .load dst address => (4, [registerWord bound dst, registerWord bound address])
  | .store address src => (5, [registerWord bound address, registerWord bound src])
  | .allocate src => (6, [registerWord bound src])
  | .release => (7, [])
  | .push src => (8, [registerWord bound src])
  | .pop dst => (9, [registerWord bound dst])
  | .emit src => (10, [registerWord bound src])
  | .branchZero src target => (11, [registerWord bound src, target])
  | .halt => (12, [])
def readFields (registers : Nat) (opcode : Nat) (operands : List (Word width)) :
    Option (Instruction width registers) :=
  match opcode, operands with
  | 0, [dst, value] => return .constant (← readRegister dst) value
  | 1, [dst, src] => return .copy (← readRegister dst) (← readRegister src)
  | 2, [dst, left, right] => return .add (← readRegister dst) (← readRegister left) (← readRegister right)
  | 3, [dst, left, right] => return .xor (← readRegister dst) (← readRegister left) (← readRegister right)
  | 4, [dst, address] => return .load (← readRegister dst) (← readRegister address)
  | 5, [address, src] => return .store (← readRegister address) (← readRegister src)
  | 6, [src] => return .allocate (← readRegister src)
  | 7, [] => some .release
  | 8, [src] => return .push (← readRegister src)
  | 9, [dst] => return .pop (← readRegister dst)
  | 10, [src] => return .emit (← readRegister src)
  | 11, [src, target] => return .branchZero (← readRegister src) target
  | 12, [] => some .halt
  | _, _ => none
def encode (bound : registers ≤ 2^width) (instruction : Instruction width registers) : List Bool :=
  bits 4 (fields bound instruction).1 ++ encodeWords width (fields bound instruction).2
def read (width registers : Nat) (input : List Bool) : Option (Instruction width registers × List Bool) := do
  let opcode ← decodeWord 4 (input.take 4)
  let (operands, rest) ← readFramedWords width (input.drop 4)
  let instruction ← readFields registers opcode.val operands
  return (instruction, rest)
def decode (width registers : Nat) (input : List Bool) : Option (Instruction width registers) := do
  let (instruction, rest) ← read width registers input
  if rest=[] then some instruction else none
def readMany (width registers : Nat) : Nat → List Bool → Option (List (Instruction width registers) × List Bool)
  | 0, input => some ([], input)
  | count+1, input => do
    let (instruction, rest) ← read width registers input
    let (instructions, suffix) ← readMany width registers count rest
    return (instruction :: instructions, suffix)
def encodeMany (bound : registers ≤ 2^width) (instructions : List (Instruction width registers)) : List Bool :=
  instructions.flatMap (encode bound)
def encodeProgram (bound : registers ≤ 2^width) (program : Program width registers) : List Bool :=
  frameCount program.size (encodeMany bound program.toList)
end Controller.Complexity.InstructionCodec

/- Definitions from Controller.Complexity.MachineInput. -/
source_context "Controller.Complexity.MachineInput"
namespace Controller.Complexity.MachineInput
open Controller.Cost Encoding
structure Image where
  width : Nat
  registers : Nat
  registerBound : registers ≤ 2^width
  program : Program width registers
  state : State width registers
def envelope (width registers : Nat) (payload : List Bool) : List Bool :=
  frameCount width (frameCount registers payload)
def encode (image : Image) : List Bool :=
  envelope image.width image.registers
    (InstructionCodec.encodeProgram image.registerBound image.program ++ MachineBridge.encodeState image.state)
def decode (input : List Bool) : Option Image := do
  let (width,rest) ← readCount input
  let (registers,rest) ← readCount rest
  if bound : registers ≤ 2^width then
    let (count,rest) ← readCount rest
    let (instructions,rest) ← InstructionCodec.readMany width registers count rest
    let state ← MachineBridge.decodeState width registers rest
    return ⟨width,registers,bound,instructions.toArray,state⟩
  else none
end Controller.Complexity.MachineInput

/- Definitions from Controller.Complexity.Reductions. -/
source_context "Controller.Complexity.Reductions"
namespace Controller.Complexity.StackMachine
open scoped BigOperators
inductive Instruction (K Q : Type)
  | push (stack : Option K) (bit : Bool) (next : Q)
  | pop (stack : Option K) (empty low high : Q)
  | peek (stack : Option K) (empty low high : Q)
  | jump (next : Q)
  | halt
structure Program (K Q : Type) where
  main : Q
  code : Q → Instruction K Q
structure State (K Q : Type) where
  pc : Option Q
  stk : Option K → List Bool
def initial (program : Program K Q) (input : List Bool) : State K Q :=
  ⟨some program.main,fun stack => match stack with | none => input | some _ => []⟩
def terminal (output : List Bool) : State K Q :=
  ⟨none,fun stack => match stack with | none => output | some _ => []⟩
def instructionStep [DecidableEq K] (instruction : Instruction K Q) (state : State K Q) : State K Q :=
  match instruction with
  | .push stack bit next => ⟨some next,Function.update state.stk stack (bit :: state.stk stack)⟩
  | .pop stack empty low high =>
    let next := match (state.stk stack).head? with | none => empty | some false => low | some true => high
    ⟨some next,Function.update state.stk stack (state.stk stack).tail⟩
  | .peek stack empty low high =>
    let next := match (state.stk stack).head? with | none => empty | some false => low | some true => high
    ⟨some next,state.stk⟩
  | .jump next => ⟨some next,state.stk⟩
  | .halt => ⟨none,state.stk⟩
def step [DecidableEq K] (program : Program K Q) (state : State K Q) : Option (State K Q) :=
  state.pc.map fun label => instructionStep (program.code label) state
def live [Fintype K] (state : State K Q) : Nat := ∑ stack : Option K, (state.stk stack).length
inductive Execution [Fintype K] [DecidableEq K] (program : Program K Q) :
    State K Q → State K Q → Nat → Nat → Prop
  | refl (state) : Execution program state state 0 (live state)
  | cons {state next final ticks peak} : step program state = some next →
      Execution program next final ticks peak → Execution program state final (ticks+1) (max (live state) peak)
def leftStack : Option K₁ → Option (Sum K₁ K₂) := Option.map Sum.inl
def rightStack : Option K₂ → Option (Sum K₁ K₂) := Option.map Sum.inr
def leftInstruction (entry : Q₂) : Instruction K₁ Q₁ → Instruction (Sum K₁ K₂) (Sum Q₁ Q₂)
  | .push stack bit next => .push (leftStack stack) bit (.inl next)
  | .pop stack empty low high => .pop (leftStack stack) (.inl empty) (.inl low) (.inl high)
  | .peek stack empty low high => .peek (leftStack stack) (.inl empty) (.inl low) (.inl high)
  | .jump next => .jump (.inl next)
  | .halt => .jump (.inr entry)
def rightInstruction : Instruction K₂ Q₂ → Instruction (Sum K₁ K₂) (Sum Q₁ Q₂)
  | .push stack bit next => .push (rightStack stack) bit (.inr next)
  | .pop stack empty low high => .pop (rightStack stack) (.inr empty) (.inr low) (.inr high)
  | .peek stack empty low high => .peek (rightStack stack) (.inr empty) (.inr low) (.inr high)
  | .jump next => .jump (.inr next)
  | .halt => .halt
/-- Sequential composition shares the input/output stack and separates private work stacks. -/
def compose (first : Program K₁ Q₁) (second : Program K₂ Q₂) :
    Program (Sum K₁ K₂) (Sum Q₁ Q₂) where
  main := .inl first.main
  code := Sum.elim (fun label => leftInstruction second.main (first.code label))
    (fun label => rightInstruction (second.code label))
/-- A concrete program computes a bit-string function within a polynomial transition bound. -/
def Computes [Fintype K] [DecidableEq K] (program : Program K Q)
    (function : List Bool → List Bool) (time : Polynomial Nat) : Prop :=
  ∀ input, ∃ ticks peak,
    Execution program (initial program input) (terminal (function input)) ticks peak ∧
      ticks ≤ time.eval input.length
end Controller.Complexity.StackMachine

/- Definitions from Controller.Complexity.ColdInterpreter. -/
source_context "Controller.Complexity.ColdInterpreter"
namespace Controller.Complexity.ColdInterpreter
open StackMachine
open scoped BigOperators
/-- Implementation witness constrained by the selected universal specifications. -/
noncomputable def Label : Type := by
  sorry
/-- Implementation witness constrained by the selected universal specifications. -/
noncomputable def program : Program (Fin 31) Label := by
  sorry
/-- Finite control for the fixed interpreter implementation. -/
noncomputable instance labelFintype : Fintype Label := by
  sorry
end Controller.Complexity.ColdInterpreter

/- Definitions from Controller.Complexity.NativePolynomial. -/
source_context "Controller.Complexity.NativePolynomial"
namespace Controller.Complexity.NativePolynomial
open StackMachine
noncomputable def parserPolynomial : Polynomial Nat := 32*Polynomial.X^4+256*Polynomial.X^3+
  484*Polynomial.X^2+643*Polynomial.X+261
noncomputable def fetchPolynomial : Polynomial Nat := 12*Polynomial.X^3+197*Polynomial.X^2+434*Polynomial.X+104
noncomputable def stepPolynomial : Polynomial Nat := fetchPolynomial+12000*(Polynomial.X+fetchPolynomial)^2+
  10003*(Polynomial.X+fetchPolynomial)+4011
noncomputable def framePolynomial : Polynomial Nat := 2*(Polynomial.X+parserPolynomial+Polynomial.X^2+
  stepPolynomial.comp (Polynomial.X^2))+45
noncomputable def timePolynomial : Polynomial Nat := Polynomial.X+2*parserPolynomial+
  Polynomial.X*(Polynomial.X^2+2*stepPolynomial.comp (Polynomial.X^2)+47)+11*framePolynomial+121
noncomputable def spacePolynomial : Polynomial Nat := 12*framePolynomial+119
end Controller.Complexity.NativePolynomial

/- Definitions from Controller.Complexity.NativeCompilation. -/
source_context "Controller.Complexity.NativeCompilation"
namespace Controller.Complexity.NativeCompilation
open StackMachine
/-- An executed image constructor and a polynomial native-time bound give a fixed finite TM2 computing the complete encoded final state in polynomial time. -/
theorem tm_polytime [Fintype K] [DecidableEq K] [Fintype Q]
    {constructor : Program K Q} {construction sourceTime : Polynomial Nat}
    (image : List Bool → MachineInput.Image)
    (final : (input : List Bool) → Controller.Cost.State (image input).width (image input).registers)
    (constructed : Computes constructor (MachineInput.encode ∘ image) construction)
    (native : ∀ input, ∃ ticks peak,
      Controller.Cost.Execution (image input).program (image input).state (final input) ticks peak ∧
      ticks ≤ sourceTime.eval input.length)
    (halted : ∀ input, (final input).halted=true) :
    Nonempty (Turing.TM2ComputableInPolyTime id id (fun input => MachineBridge.encodeState (final input))) := by
  sorry
end Controller.Complexity.NativeCompilation

/- Definitions from Controller.Complexity.ImageCanonical. -/
source_context "Controller.Complexity.ImageCanonical"
namespace Controller.Complexity.ImageCanonical
open Encoding
/-- Every accepted encoded image executes its source run in the cold binary interpreter within the displayed literal time and space polynomials. -/
theorem decoded_execution (input : List Bool) (image : MachineInput.Image)
    (decoded : MachineInput.decode input=some image)
    {final : Controller.Cost.State image.width image.registers} {nativeTicks nativePeak}
    (native : Controller.Cost.Execution image.program image.state final nativeTicks nativePeak)
    (halted : final.halted=true) :
    ∃ ticks peak, StackMachine.Execution ColdInterpreter.program
      (StackMachine.initial ColdInterpreter.program input) (StackMachine.terminal (MachineBridge.encodeState final)) ticks peak ∧
      ticks ≤ NativePolynomial.timePolynomial.eval (input.length+nativeTicks+1) ∧
      peak ≤ NativePolynomial.spacePolynomial.eval (input.length+nativeTicks+1) := by
  sorry
end Controller.Complexity.ImageCanonical

/- Definitions from Controller.Complexity.ReadOnlyInput. -/
source_context "Controller.Complexity.ReadOnlyInput"
namespace Controller.Complexity.ReadOnlyInput
structure Tape where
  left : List Bool
  right : List Bool
  deriving DecidableEq
def start (input : List Bool) : Tape := ⟨[],input⟩
def symbol (tape : Tape) := tape.right.head?
def moveLeft (tape : Tape) : Tape :=
  match tape.left with
  | [] => tape
  | bit :: rest => ⟨rest,bit :: tape.right⟩
def moveRight (tape : Tape) : Tape :=
  match tape.right with
  | [] => tape
  | bit :: rest => ⟨bit :: tape.left,rest⟩
end Controller.Complexity.ReadOnlyInput

/- Definitions from Controller.Complexity.SpaceMachine. -/
source_context "Controller.Complexity.SpaceMachine"
namespace Controller.Complexity.SpaceMachine
open scoped BigOperators
inductive Instruction (K Q : Type)
  | push (stack : K) (bit : Bool) (next : Q)
  | pop (stack : K) (empty low high : Q)
  | peek (stack : K) (empty low high : Q)
  | readInput (eof low high : Q)
  | atStart (yes no : Q)
  | left (next : Q)
  | right (next : Q)
  | emit (bit : Bool) (next : Q)
  | jump (next : Q)
  | halt
structure Program (K Q : Type) where
  main : Q
  code : Q → Instruction K Q
structure State (K Q : Type) where
  pc : Option Q
  tape : ReadOnlyInput.Tape
  work : K → List Bool
  output : List Bool
def initial (program : Program K Q) (input : List Bool) : State K Q :=
  ⟨some program.main,ReadOnlyInput.start input,fun _ => [],[]⟩
def advance (state : State K Q) (next : Q) : State K Q := { state with pc := some next }
def observed (empty low high : Q) : Option Bool → Q
  | none => empty
  | some false => low
  | some true => high
def instructionStep [DecidableEq K] (instruction : Instruction K Q) (state : State K Q) : State K Q :=
  match instruction with
  | .push port bit next => { advance state next with work := Function.update state.work port (bit :: state.work port) }
  | .pop port empty low high =>
    { advance state (observed empty low high (state.work port).head?) with
      work := Function.update state.work port (state.work port).tail }
  | .peek port empty low high => advance state (observed empty low high (state.work port).head?)
  | .readInput eof low high => advance state (observed eof low high (ReadOnlyInput.symbol state.tape))
  | .atStart yes no => advance state (if state.tape.left.isEmpty then yes else no)
  | .left next => { advance state next with tape := ReadOnlyInput.moveLeft state.tape }
  | .right next => { advance state next with tape := ReadOnlyInput.moveRight state.tape }
  | .emit bit next => { advance state next with output := bit :: state.output }
  | .jump next => advance state next
  | .halt => { state with pc := none }
def step [DecidableEq K] (program : Program K Q) (state : State K Q) : Option (State K Q) :=
  state.pc.map fun label => instructionStep (program.code label) state
def workspace [Fintype K] (state : State K Q) : Nat := ∑ port, (state.work port).length
inductive Execution [Fintype K] [DecidableEq K] (program : Program K Q) :
    State K Q → State K Q → Nat → Nat → Prop
  | refl (state) : Execution program state state 0 (workspace state)
  | cons {state next final ticks peak} : step program state=some next →
      Execution program next final ticks peak → Execution program state final (ticks+1) (max (workspace state) peak)
end Controller.Complexity.SpaceMachine

/- Definitions from Controller.Complexity.LogSpaceBounds. -/
source_context "Controller.Complexity.LogSpaceBounds"
namespace Controller.Complexity.LogSpaceBounds
open SpaceMachine
def bits (length : Nat) := Nat.log 2 (length+2)+1
def degree (constant banks : Nat) := 2*constant*banks
def timeBound (labels banks constant length : Nat) :=
  (labels+1)*2^(degree constant banks)*(length+2)^(degree constant banks+1)
/-- A finite actual transducer computes its output stream within a logarithmic
work-bit bound. Finite control is part of the predicate; its enumeration is
needed for configuration counting, while the execution relation does not need it.
Halting and the output relation are proved for every input. -/
def Computes [Fintype K] [DecidableEq K] (program : SpaceMachine.Program K Q)
    (function : List Bool → List Bool) (constant : Nat) : Prop :=
  Finite Q ∧ ∀ input, ∃ final ticks peak, SpaceMachine.Execution program (initial program input) final ticks peak ∧
    final.pc=none ∧ final.output.reverse=function input ∧ peak ≤ constant*bits input.length
end Controller.Complexity.LogSpaceBounds

/- Definitions from Controller.Complexity.SpaceLookup. -/
source_context "Controller.Complexity.SpaceLookup"
namespace Controller.Complexity.SpaceLookup
open SpaceMachine
abbrev Bank (K : Type) := K ⊕ Fin 3
abbrev Label (Q : Type) := Q ⊕ ((Q × Fin 7) ⊕ (Bool ⊕ Unit))
end Controller.Complexity.SpaceLookup

/- Definitions from Controller.Complexity.SpaceBuffers. -/
source_context "Controller.Complexity.SpaceBuffers"
namespace Controller.Complexity.SpaceBuffers
open SpaceMachine
open scoped BigOperators
abbrev CopyLabel := Fin 4 ⊕ Fin 6
end Controller.Complexity.SpaceBuffers

/- Definitions from Controller.Complexity.SpaceErase. -/
source_context "Controller.Complexity.SpaceErase"
namespace Controller.Complexity.SpaceErase
open SpaceMachine
abbrev Label (n : Nat) := Fin (n+1) × Bool
end Controller.Complexity.SpaceErase

/- Definitions from Controller.Complexity.SpaceRequestSetup. -/
source_context "Controller.Complexity.SpaceRequestSetup"
namespace Controller.Complexity.SpaceRequestSetup
open SpaceMachine
abbrev Bank (K J : Type) := SpaceLookup.Bank K ⊕ J
abbrev Label (n : Nat) := (SpaceErase.Label n ⊕ SpaceBuffers.CopyLabel) ⊕ Fin 3
end Controller.Complexity.SpaceRequestSetup

/- Definitions from Controller.Complexity.SpaceRequest. -/
source_context "Controller.Complexity.SpaceRequest"
namespace Controller.Complexity.SpaceRequest
open SpaceMachine
abbrev Label (n : Nat) (Q : Type) := SpaceRequestSetup.Label n ⊕ SpaceLookup.Label Q
end Controller.Complexity.SpaceRequest

/- Definitions from Controller.Complexity.SpaceVirtual. -/
source_context "Controller.Complexity.SpaceVirtual"
namespace Controller.Complexity.SpaceVirtual
open SpaceMachine
abbrev Caller (B : Type) := B ⊕ Bool
abbrev Bank (A B : Type) := SpaceRequestSetup.Bank A (Caller B)
abbrev Label (n : Nat) (P Q : Type) :=
  Q ⊕ ((Q × SpaceRequest.Label n P) ⊕ (Q ⊕ ((Q × Fin 7) ⊕ (Q × Fin 7))))
/-- Implementation witness constrained by the selected universal specifications. -/
noncomputable def program (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    (enumeration : Fin n ≃ SpaceLookup.Bank A) : SpaceMachine.Program (Bank A B) (Label n P Q) := by
  sorry
end Controller.Complexity.SpaceVirtual

/- Definitions from Controller.Complexity.SpaceLogGrowth. -/
source_context "Controller.Complexity.SpaceLogGrowth"
namespace Controller.Complexity.SpaceLogGrowth
def constant (labels banks coefficient : Nat) :=
  (labels+1)*2^(LogSpaceBounds.degree coefficient banks)+LogSpaceBounds.degree coefficient banks+3
end Controller.Complexity.SpaceLogGrowth

/- Definitions from Controller.Complexity.SpaceComposition. -/
source_context "Controller.Complexity.SpaceComposition"
namespace Controller.Complexity.SpaceComposition
def constant (firstLabels firstBanks firstConstant secondConstant : Nat) :=
  firstConstant+(secondConstant+2)*SpaceLogGrowth.constant firstLabels firstBanks firstConstant+2
end Controller.Complexity.SpaceComposition

/- Definitions from Controller.Complexity.SpaceInputTape. -/
source_context "Controller.Complexity.SpaceInputTape"
namespace Controller.Complexity.SpaceInputTape
open Turing
inductive Symbol
  | blank
  | start
  | stop
  | bit (value : Bool)
  deriving DecidableEq, Fintype
instance : Inhabited Symbol := ⟨.blank⟩
def encode (source : ReadOnlyInput.Tape) : Tape Symbol :=
  Tape.mk₂ (source.left.map Symbol.bit++[.start]) (source.right.map Symbol.bit++[.stop])
def observed : Symbol → Option Bool
  | .bit value => some value
  | _ => none
end Controller.Complexity.SpaceInputTape

/- Definitions from Controller.Complexity.SpaceWorkTape. -/
source_context "Controller.Complexity.SpaceWorkTape"
namespace Controller.Complexity.SpaceWorkTape
open Turing
inductive Symbol
  | blank
  | bottom
  | bit (value : Bool)
  deriving DecidableEq, Fintype
instance : Inhabited Symbol := ⟨.blank⟩
def blank : Tape Symbol := ⟨.blank,ListBlank.mk [],ListBlank.mk []⟩
def encode (bits : List Bool) : Tape Symbol :=
  ⟨.blank,ListBlank.mk (bits.map Symbol.bit++[.bottom]),ListBlank.mk []⟩
def observed : Symbol → Option Bool
  | .bit value => some value
  | .blank | .bottom => none
end Controller.Complexity.SpaceWorkTape

/- Definitions from Controller.Complexity.SpaceTapeMachine. -/
source_context "Controller.Complexity.SpaceTapeMachine"
namespace Controller.Complexity.SpaceTapeMachine
open Turing
inductive Label (n : Nat) (K Q : Type)
  | init (index : Fin (n+1))
  | run (label : Q)
  | pop (port : K) (empty low high : Q)
  | peek (port : K) (empty low high : Q)
  | left (next : Q)
  | start (yes no : Q)
  deriving DecidableEq, Fintype
structure Action (n : Nat) (K Q : Type) where
  next : Option (Label n K Q)
  work : Option (K × Option SpaceWorkTape.Symbol × Option Dir) := none
  input : Option Dir := none
  output : Option Bool := none
structure State (n : Nat) (K Q : Type) where
  pc : Option (Label n K Q)
  input : Tape SpaceInputTape.Symbol
  work : K → Tape SpaceWorkTape.Symbol
  heads : K → Int
  output : List Bool
def delta (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (label : Label n K Q) (input : SpaceInputTape.Symbol) (work : K → SpaceWorkTape.Symbol) : Action n K Q :=
  match label with
  | .init index =>
      if available : index.val<n then
        ⟨some (.init ⟨index.val+1,by omega⟩),some (enumeration ⟨index.val,available⟩,some .bottom,some .right),none,none⟩
      else ⟨some (.run program.main),none,none,none⟩
  | .run label => match program.code label with
      | .push port bit next => ⟨some (.run next),some (port,some (.bit bit),some .right),none,none⟩
      | .pop port empty low high => ⟨some (.pop port empty low high),some (port,none,some .left),none,none⟩
      | .peek port empty low high => ⟨some (.peek port empty low high),some (port,none,some .left),none,none⟩
      | .readInput eof low high => ⟨some (.run (SpaceMachine.observed eof low high (SpaceInputTape.observed input))),none,none,none⟩
      | .atStart yes no => ⟨some (.start yes no),none,some .left,none⟩
      | .left next => ⟨some (.left next),none,some .left,none⟩
      | .right next => ⟨some (.run next),none,if input=.stop then none else some .right,none⟩
      | .emit bit next => ⟨some (.run next),none,none,some bit⟩
      | .jump next => ⟨some (.run next),none,none,none⟩
      | .halt => ⟨none,none,none,none⟩
  | .pop port empty low high =>
      match work port with
      | .bit bit => ⟨some (.run (if bit then high else low)),some (port,some .blank,none),none,none⟩
      | .bottom => ⟨some (.run empty),some (port,none,some .right),none,none⟩
      | .blank => ⟨none,none,none,none⟩
  | .peek port empty low high =>
      ⟨some (.run (SpaceMachine.observed empty low high (SpaceWorkTape.observed (work port)))),
        some (port,none,some .right),none,none⟩
  | .left next => ⟨some (.run next),none,if input=.start then some .right else none,none⟩
  | .start yes no => ⟨some (.run (if input=.start then yes else no)),none,some .right,none⟩
def shift : Option Dir → Int
  | none => 0
  | some .left => -1
  | some .right => 1
def operate (write : Option SpaceWorkTape.Symbol) (move : Option Dir) (tape : Tape SpaceWorkTape.Symbol) : Tape SpaceWorkTape.Symbol :=
  let written := write.elim tape fun symbol => tape.write symbol
  move.elim written fun direction => written.move direction
def apply [DecidableEq K] (action : Action n K Q) (state : State n K Q) : State n K Q where
  pc := action.next
  input := action.input.elim state.input fun direction => state.input.move direction
  work := action.work.elim state.work fun (port,write,move) => Function.update state.work port (operate write move (state.work port))
  heads := action.work.elim state.heads fun (port,_,move) => Function.update state.heads port (state.heads port+shift move)
  output := action.output.elim state.output fun bit => bit::state.output
def step [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (state : State n K Q) : Option (State n K Q) :=
  state.pc.map fun label => apply (delta enumeration program label state.input.head (fun port => (state.work port).head)) state
def initial (input : List Bool) : State n K Q :=
  ⟨some (.init ⟨0,by omega⟩),SpaceInputTape.encode (ReadOnlyInput.start input),
    fun _ => SpaceWorkTape.blank,fun _ => 0,[]⟩
def configuration (source : SpaceMachine.State K Q) : State n K Q :=
  ⟨source.pc.map Label.run,SpaceInputTape.encode source.tape,
    fun port => SpaceWorkTape.encode (source.work port),fun port => (source.work port).length+1,source.output⟩
end Controller.Complexity.SpaceTapeMachine

/- Definitions from Controller.Complexity.SpaceTapeRun. -/
source_context "Controller.Complexity.SpaceTapeRun"
namespace Controller.Complexity.SpaceTapeRun
open SpaceTapeMachine SpaceMachine
def Within (capacity : Nat) (state : SpaceTapeMachine.State n K Q) : Prop :=
  ∀ port, 0 ≤ state.heads port ∧ state.heads port < (capacity : Int)
inductive Run [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (capacity : Nat) : SpaceTapeMachine.State n K Q → SpaceTapeMachine.State n K Q → Nat → Prop
  | refl {state} : Within capacity state → Run enumeration program capacity state state 0
  | cons {state next final ticks} : SpaceTapeMachine.step enumeration program state=some next →
      Within capacity state → Run enumeration program capacity next final ticks →
      Run enumeration program capacity state final (ticks+1)
end Controller.Complexity.SpaceTapeRun

/- Definitions from Controller.Complexity.SpaceTapeBridge. -/
source_context "Controller.Complexity.SpaceTapeBridge"
namespace Controller.Complexity.SpaceTapeBridge
open SpaceMachine SpaceTapeMachine SpaceTapeRun
/-- Two executed logarithmic-workspace programs have a composed tape execution with the displayed workspace capacity and time bound, starting from blank work tapes. -/
theorem composed [Fintype A] [Fintype B] [Fintype P] [Fintype Q] [DecidableEq A] [DecidableEq B]
    (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    (lookup : Fin n ≃ SpaceLookup.Bank A) (banks : Fin m ≃ SpaceVirtual.Bank A B)
    {function target firstConstant secondConstant}
    (firstComputes : LogSpaceBounds.Computes first function firstConstant)
    (secondComputes : LogSpaceBounds.Computes second target secondConstant) (input : List Bool) :
    ∃ final tapeTicks, Run banks (SpaceVirtual.program first second lookup)
      ((SpaceComposition.constant (Fintype.card P) (Fintype.card A) firstConstant secondConstant+2)*
        LogSpaceBounds.bits input.length)
      (SpaceTapeMachine.initial input) (configuration final) tapeTicks ∧
      final.pc=none ∧ final.output.reverse=target (function input) ∧
      tapeTicks ≤ m+1+2*LogSpaceBounds.timeBound (Fintype.card (SpaceVirtual.Label n P Q))
        (Fintype.card (SpaceVirtual.Bank A B))
        (SpaceComposition.constant (Fintype.card P) (Fintype.card A) firstConstant secondConstant) input.length := by
  sorry
end Controller.Complexity.SpaceTapeBridge

/- Definitions from Controller.Complexity.SpaceTapeAllocation. -/
source_context "Controller.Complexity.SpaceTapeAllocation"
namespace Controller.Complexity.SpaceTapeAllocation
open SpaceTapeMachine SpaceTapeRun
open scoped BigOperators
inductive Covered [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (cells : K → Finset Int) : SpaceTapeMachine.State n K Q → SpaceTapeMachine.State n K Q → Nat → Prop
  | refl {state} : (∀ port, state.heads port ∈ cells port) → Covered enumeration program cells state state 0
  | cons {state next final ticks} : SpaceTapeMachine.step enumeration program state=some next →
      (∀ port, state.heads port ∈ cells port) → Covered enumeration program cells next final ticks →
      Covered enumeration program cells state final (ticks+1)
end Controller.Complexity.SpaceTapeAllocation

/- Definitions from Controller.Complexity.SpaceTapeErasure. -/
source_context "Controller.Complexity.SpaceTapeErasure"
namespace Controller.Complexity.SpaceTapeErasure
open SpaceTapeMachine SpaceTapeRun
open scoped BigOperators
structure Configuration (n : Nat) (K Q : Type) where
  pc : Option (Label n K Q)
  input : Turing.Tape SpaceInputTape.Symbol
  work : K → Turing.Tape SpaceWorkTape.Symbol
  output : List Bool
def erase (state : SpaceTapeMachine.State n K Q) : Configuration n K Q :=
  ⟨state.pc,state.input,state.work,state.output⟩
def apply [DecidableEq K] (action : Action n K Q) (state : Configuration n K Q) : Configuration n K Q where
  pc := action.next
  input := action.input.elim state.input fun direction => state.input.move direction
  work := action.work.elim state.work fun (port,write,move) =>
    Function.update state.work port (operate write move (state.work port))
  output := action.output.elim state.output fun bit => bit::state.output
def step [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (state : Configuration n K Q) : Option (Configuration n K Q) :=
  state.pc.map fun label => apply (delta enumeration program label state.input.head (fun port => (state.work port).head)) state
/-- Erasing allocation bookkeeping preserves the ordinary tape execution and covers all visited work cells within the stated logarithmic bound. -/
theorem logspace [Fintype K] [DecidableEq K] [Fintype Q]
    (enumeration : Fin n ≃ K) {program : SpaceMachine.Program K Q} {function constant}
    (computed : LogSpaceBounds.Computes program function constant) (input : List Bool) :
    ∃ final ticks allocated,
      Nonempty (StateTransition.EvalsToInTime (step enumeration program)
        (erase (SpaceTapeMachine.initial input)) (some (erase (configuration final))) ticks) ∧
      SpaceTapeAllocation.Covered enumeration program allocated (SpaceTapeMachine.initial input) (configuration final) ticks ∧
      (erase (configuration (n := n) final)).pc=none ∧
      (erase (configuration (n := n) final)).output.reverse=function input ∧
      (∑ port, (allocated port).card)=Fintype.card K*(constant+2)*LogSpaceBounds.bits input.length ∧
      ticks ≤ n+1+2*LogSpaceBounds.timeBound (Fintype.card Q) (Fintype.card K) constant input.length := by
  sorry
end Controller.Complexity.SpaceTapeErasure

/- Definitions from Controller.Complexity.ParameterMajorant. -/
source_context "Controller.Complexity.ParameterMajorant"
namespace Controller.Complexity.ParameterMajorant
def maximum (function : Nat → Nat) : Nat → Nat
  | 0 => function 0
  | n+1 => max (maximum function n) (function (n+1))
end Controller.Complexity.ParameterMajorant

/- Definitions from Controller.Complexity.ParameterBounds. -/
source_context "Controller.Complexity.ParameterBounds"
namespace Controller.Complexity.ParameterBounds
def degree (first second : Nat) := first+(first+1)*second
def coefficient (first second parameter : Nat → Nat) (secondDegree : Nat) (k : Nat) :=
  first k+ParameterMajorant.maximum second (parameter k)*(first k+1)^secondDegree
end Controller.Complexity.ParameterBounds

/- Definitions from Controller.Complexity.ParameterRuntime. -/
source_context "Controller.Complexity.ParameterRuntime"
namespace Controller.Complexity.ParameterRuntime
open StackMachine
def Computes [Fintype K] [DecidableEq K] (program : Program K Q)
    (function : List Bool → List Bool) (parameter : List Bool → Nat)
    (coefficient : Nat → Nat) (degree : Nat) : Prop :=
  Finite Q ∧ Computable coefficient ∧ ∀ input, ∃ ticks peak,
    Execution program (initial program input) (terminal (function input)) ticks peak ∧
      ticks ≤ coefficient (parameter input)*(input.length+1)^degree
end Controller.Complexity.ParameterRuntime

/- Definitions from Controller.Complexity.ParameterReduction. -/
source_context "Controller.Complexity.ParameterReduction"
namespace Controller.Complexity.ParameterReduction
open StackMachine
def Reduces [Fintype K] [DecidableEq K] (program : Program K Q) (function : List Bool → List Bool)
    (source target : Set (List Bool)) (sourceParameter targetParameter : List Bool → Nat)
    (coefficient : Nat → Nat) (degree : Nat) (parameterBound : Nat → Nat) : Prop :=
  ParameterRuntime.Computes program function sourceParameter coefficient degree ∧
    Computable parameterBound ∧ (∀ input, targetParameter (function input) ≤ parameterBound (sourceParameter input)) ∧
    ∀ input, input ∈ source ↔ function input ∈ target
/-- Executed parameterized many-one reductions compose with computable coefficient and parameter bounds; neither parameter-growth bound must be monotone. -/
theorem compose [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {first : Program A P} {second : Program B Q} {function target firstLanguage middleLanguage lastLanguage}
    {sourceParameter middleParameter lastParameter firstCoefficient secondCoefficient firstDegree secondDegree firstBound secondBound}
    (firstReduction : Reduces first function firstLanguage middleLanguage sourceParameter middleParameter firstCoefficient firstDegree firstBound)
    (secondReduction : Reduces second target middleLanguage lastLanguage middleParameter lastParameter secondCoefficient secondDegree secondBound) :
    Reduces (StackMachine.compose first second) (target ∘ function) firstLanguage lastLanguage sourceParameter lastParameter
      (ParameterBounds.coefficient firstCoefficient secondCoefficient firstBound secondDegree)
      (ParameterBounds.degree firstDegree secondDegree) (ParameterMajorant.maximum secondBound ∘ firstBound) := by
  sorry
end Controller.Complexity.ParameterReduction

/- Definitions from Controller.Complexity.ParameterTM. -/
source_context "Controller.Complexity.ParameterTM"
namespace Controller.Complexity.ParameterTM
open StackMachine
/-- One fixed finite TM2 and fixed alphabet equivalences realize every input of the parameterized computation within its supplied time bound. -/
theorem realization [Fintype K] [DecidableEq K] {program : Program K Q}
    {function parameter coefficient degree}
    (computed : ParameterRuntime.Computes program function parameter coefficient degree) :
    ∃ (machine : Turing.FinTM2) (inputAlphabet : Bool ≃ machine.Γ machine.k₀)
      (outputAlphabet : Bool ≃ machine.Γ machine.k₁),
      ∀ input, Nonempty (Turing.TM2OutputsInTime machine (input.map inputAlphabet)
        (some ((function input).map outputAlphabet)) (coefficient (parameter input)*(input.length+1)^degree)) := by
  sorry
end Controller.Complexity.ParameterTM

end_source_context
