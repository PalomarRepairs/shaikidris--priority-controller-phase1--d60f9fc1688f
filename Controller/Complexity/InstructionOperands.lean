module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.OperandLoop
public import Controller.Complexity.OpcodeRoles

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Saved operand payload and cardinality are copied by finite programs.
The opcode-role decoder guards a counted pass over that copied payload.
The original tag, payload, cardinality and global headers remain available. -/
namespace Controller.Complexity.InstructionOperands
open StackMachine WordReader
open scoped BigOperators

def payloadPorts : Option Bool ↪ Port :=
  StackFrames.threePorts (some 11) (some 0) (some 2) (by decide) (by decide) (by decide)

def countPorts : Option Bool ↪ Port :=
  StackFrames.threePorts (some 12) (some 10) (some 2) (by decide) (by decide) (by decide)

theorem payloadPorts_apply (port : Option Bool) : payloadPorts port=
    (match port with | none => some 11 | some false => some 0 | some true => some 2) := rfl

theorem countPorts_apply (port : Option Bool) : countPorts port=
    (match port with | none => some 12 | some false => some 10 | some true => some 2) := rfl

def payloadMachine := StackFrames.relocate payloadPorts StackCopy.program
def countMachine := StackFrames.relocate countPorts StackCopy.program
def setup := link payloadMachine countMachine
def body := link setup OperandLoop.program
def program := GuardedLink.program OpcodeRoles.machine body none Option.isNone

theorem setup_execution (frame : Port → List Bool) (roles : List Bool) (count : Nat)
    (clean : frame none=[]) (wordClean : frame (some 1)=[]) (scratchClean : frame (some 2)=[])
    (countClean : frame (some 10)=[]) (boundClean : frame (some 16)=[]) (secondClean : frame (some 17)=[])
    (roleStored : frame (some 18)=roles) (countStored : frame (some 12)=List.replicate count true) :
    ∃ peak, Execution setup ⟨some setup.main,frame⟩
      ⟨none,OperandLoop.data frame roles count [] (frame (some 11)++frame (some 0)) []⟩
      (5*(frame (some 11)).length+5*count+8) peak := by
  obtain ⟨payloadPeak,payloadRun⟩ := StackCopy.ready_execution payloadPorts frame (by simpa only [payloadPorts_apply] using scratchClean)
  let moved := Function.update frame (some 0) (frame (some 11)++frame (some 0))
  change Execution payloadMachine ⟨some payloadMachine.main,frame⟩ ⟨none,moved⟩ _ _ at payloadRun
  obtain ⟨countPeak,countRun⟩ := StackCopy.ready_execution countPorts moved (by simp [moved, countPorts_apply, scratchClean])
  have endpoint : Function.update moved (countPorts (some false)) (moved (countPorts none)++moved (countPorts (some false)))=
      OperandLoop.data frame roles count [] (frame (some 11)++frame (some 0)) [] := by
    funext target
    by_cases hn : target=some 10
    · subst target; simp [moved, countPorts_apply, OperandLoop.data_at, countStored, countClean]
    by_cases hs : target=some 0
    · subst target; simp [moved, countPorts_apply, OperandLoop.data_at]
    by_cases hc : target=none
    · subst target; simp [moved, countPorts_apply, OperandLoop.data_at, clean]
    by_cases hw : target=some 1
    · subst target; simp [moved, countPorts_apply, OperandLoop.data_at, wordClean]
    by_cases ht : target=some 2
    · subst target; simp [moved, countPorts_apply, OperandLoop.data_at, scratchClean]
    by_cases ha : target=some 16
    · subst target; simp [moved, countPorts_apply, OperandLoop.data_at, boundClean]
    by_cases hb : target=some 17
    · subst target; simp [moved, countPorts_apply, OperandLoop.data_at, secondClean]
    by_cases hr : target=some 18
    · subst target; simp [moved, countPorts_apply, OperandLoop.data_at, roleStored]
    simp [moved, countPorts_apply, OperandLoop.data_at, hn, hs, hc, hw, ht, ha, hb, hr]
  rw [endpoint] at countRun
  have copiedTime : 5*(moved (countPorts none)).length+4=5*count+4 := by simp [moved, countPorts_apply, countStored]
  rw [copiedTime] at countRun
  have trace := payloadRun.link countRun
  have totalTime : (5*(frame (payloadPorts none)).length+4)+(5*count+4)=5*(frame (some 11)).length+5*count+8 := by
    simp only [payloadPorts_apply]
    omega
  exact ⟨max payloadPeak countPeak,by simpa only [setup, countMachine, totalTime] using trace⟩

theorem body_execution (frame : Port → List Bool) (width registers : Nat) (roles : List Bool)
    (clean : frame none=[]) (wordClean : frame (some 1)=[]) (scratchClean : frame (some 2)=[])
    (countClean : frame (some 10)=[]) (boundClean : frame (some 16)=[]) (secondClean : frame (some 17)=[])
    (roleStored : frame (some 18)=roles) (countStored : frame (some 12)=List.replicate roles.length true)
    (widthStored : frame (some 8)=List.replicate width true) (saved : frame (some 9)=List.replicate registers true) :
    ∃ ticks peak, Execution body ⟨some body.main,frame⟩
      ⟨none,OperandLoop.endpoint frame (OperandLoop.scan width registers roles (frame (some 11)++frame (some 0)))⟩ ticks peak ∧
      ticks ≤ 5*(frame (some 11)).length+roles.length*(width*(4*registers+19)+6*registers+32)+10 := by
  obtain ⟨setupPeak,setupRun⟩ := setup_execution frame roles roles.length clean wordClean scratchClean countClean boundClean secondClean roleStored countStored
  obtain ⟨loopTicks,loopPeak,loopRun,bound⟩ := OperandLoop.total_execution frame width registers roles
    (frame (some 11)++frame (some 0)) widthStored saved
  have trace := setupRun.link loopRun
  refine ⟨_,_,trace,?_⟩
  have identity : 5*(frame (some 11)).length+roles.length*(width*(4*registers+19)+6*registers+32)+10=
      (5*(frame (some 11)).length+5*roles.length+8)+
        (roles.length*(width*(4*registers+19)+6*registers+27)+2) := by ring
  rw [identity]
  omega

theorem execution (frame : Port → List Bool) (width registers : Nat) (opcode : Fin 16) (roles : List Bool)
    (roleDecoded : OpcodeRoles.roles opcode=some roles)
    (tagStored : frame (some 13)=(Encoding.bits 4 opcode.val).reverse)
    (clean : frame none=[]) (wordClean : frame (some 1)=[]) (scratchClean : frame (some 2)=[])
    (countClean : frame (some 10)=[]) (boundClean : frame (some 16)=[]) (secondClean : frame (some 17)=[])
    (roleClean : frame (some 18)=[]) (countStored : frame (some 12)=List.replicate roles.length true)
    (widthStored : frame (some 8)=List.replicate width true) (saved : frame (some 9)=List.replicate registers true) :
    ∃ ticks peak, Execution program ⟨some program.main,frame⟩
      ⟨none,OperandLoop.endpoint (Function.update frame (some 18) roles)
        (OperandLoop.scan width registers roles (frame (some 11)++frame (some 0)))⟩ ticks peak ∧
      ticks ≤ 5*(frame (some 11)).length+roles.length*(width*(4*registers+19)+6*registers+32)+24 := by
  obtain ⟨roleTicks,rolePeak,roleRun,roleBound⟩ := OpcodeRoles.framed_execution frame opcode tagStored roleClean clean
  simp only [roleDecoded, Option.getD_some, Option.isSome_some, ite_true] at roleRun
  have status : (Function.update frame (some 18) roles) none=[] := by simp [clean]
  rw [ColdInput.update_empty _ none status] at roleRun
  obtain ⟨bodyTicks,bodyPeak,bodyRun,bodyBound⟩ := body_execution (Function.update frame (some 18) roles) width registers roles
    status (by simp [wordClean]) (by simp [scratchClean]) (by simp [countClean]) (by simp [boundClean])
    (by simp [secondClean]) (by simp) (by simp [countStored]) (by simp [widthStored]) (by simp [saved])
  simp only [Function.update_of_ne (show (some 11 : Port) ≠ some 18 by decide),
    Function.update_of_ne (show (some 0 : Port) ≠ some 18 by decide)] at bodyRun bodyBound
  have trace := GuardedLink.success none Option.isNone roleRun bodyRun (by simp [clean])
  exact ⟨_,_,trace,by omega⟩

end Controller.Complexity.InstructionOperands
