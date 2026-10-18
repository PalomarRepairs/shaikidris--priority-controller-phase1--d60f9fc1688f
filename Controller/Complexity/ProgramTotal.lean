module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.ProgramReader
public import Controller.Complexity.ProgramSyntax

public import Mathlib.Tactic.Ring

@[expose] public section

/-! All-input program parsing uses a storage budget preserved by successful
instruction collection. An invalid instruction halts through the actual guard
without executing another iteration or reversing the partial program buffer. -/
namespace Controller.Complexity.ProgramTotal
open StackMachine WordReader ProgramReader

structure Workspace (frame : Port → List Bool) (width registers : Nat) : Prop where
  stored : frame (some 8)=List.replicate width true
  saved : frame (some 9)=List.replicate registers true
  loopEmpty : frame (some 10)=[]
  payloadEmpty : frame (some 11)=[]
  countEmpty : frame (some 12)=[]
  tagEmpty : frame (some 13)=[]
  rangeEmpty : frame (some 16)=[]
  scratchEmpty : frame (some 17)=[]
  roleEmpty : frame (some 18)=[]
  temporaryEmpty : frame (some 20)=[]

def cost (budget : Nat) : Nat := 4*budget^3+64*budget^2+200*budget+400

theorem ambient_fields (frame : Port → List Bool) (count : Nat) (buffer : List Bool)
    (countEmpty : frame (some 14)=[]) (bufferEmpty : frame (some 19)=[]) :
    ambientBits (fields frame count buffer)=ambientBits frame+count+buffer.length := by
  have first := ColdInput.ambient_saved frame 14 (by decide) (by decide) (by decide) (List.replicate count true) countEmpty
  have second := ColdInput.ambient_saved (Function.update frame (some 14) (List.replicate count true)) 19
    (by decide) (by decide) (by decide) buffer (by simpa using bufferEmpty)
  simpa only [fields, first, List.length_replicate] using second

theorem frontend_cost (size budget : Nat) (bounded : size ≤ budget) :
    4*size^3+52*size^2+56*size+119+3 ≤ cost budget := by
  have cube := Nat.pow_le_pow_left bounded 3
  have square := Nat.pow_le_pow_left bounded 2
  unfold cost
  omega

theorem valid_cost (width registers budget : Nat) (widthBound : width ≤ budget) (registerBound : registers ≤ budget) :
    12*width*registers+144*width+18*registers+319+1 ≤ cost budget := by
  have product := Nat.mul_le_mul_left 12 (Nat.mul_le_mul widthBound registerBound)
  have identity : 12*width*registers=12*(width*registers) := by ring
  have square : budget*budget=budget^2 := by ring
  rw [square] at product
  unfold cost
  rw [identity]
  omega

theorem loop_total (frame : Port → List Bool) (bound : registers ≤ 2^width) (count : Nat)
    (source buffer : List Bool) (budget : Nat) (ready : Workspace frame width registers)
    (countEmpty : frame (some 14)=[]) (bufferEmpty : frame (some 19)=[])
    (mass : count+source.length+buffer.length+ambientBits frame ≤ budget) :
    ∃ final ticks peak, Execution loop ⟨some loop.main,data frame count source buffer⟩ final ticks peak ∧
      final.pc=none ∧ Option.isNone (final.stk none).head?=(InstructionCodec.readMany width registers count source).isSome ∧
      ticks ≤ count*cost budget+2 := by
  induction count generalizing source buffer with
  | zero =>
    have trace := CountLoop.empty body (some 14) none Option.isNone (data frame 0 source buffer) (by simp [data_at])
    exact ⟨_,2,_,trace,rfl,by simp [data_at, InstructionCodec.readMany],by simp⟩
  | succ count ih =>
    have counted : data frame (count+1) source buffer (some 14)=true :: List.replicate count true := by simp [data_at, List.replicate_succ]
    cases decoded : InstructionCodec.read width registers source with
    | some pair =>
      rcases pair with ⟨instruction,suffix⟩
      have canonical := ProgramSyntax.read_inverse bound source instruction suffix decoded
      have nextMass : count+suffix.length+((InstructionCodec.encode bound instruction).reverse++buffer).length+ambientBits frame ≤ budget := by
        have lengths : source.length=(InstructionCodec.encode bound instruction).length+suffix.length := by
          rw [canonical, List.length_append]
        simp only [List.length_append, List.length_reverse]
        omega
      obtain ⟨final,tailTicks,tailPeak,tailRun,tailHalted,tailStatus,tailBound⟩ := ih suffix
        ((InstructionCodec.encode bound instruction).reverse++buffer) nextMass
      have terminal : final=⟨none,final.stk⟩ := congrArg₂ State.mk tailHalted rfl
      rw [terminal] at tailRun
      obtain ⟨bodyTicks,bodyPeak,bodyRun,bodyBound⟩ := body_execution frame bound instruction count suffix buffer
        ready.stored ready.saved ready.loopEmpty ready.payloadEmpty ready.countEmpty ready.tagEmpty ready.rangeEmpty ready.scratchEmpty ready.roleEmpty ready.temporaryEmpty
      rw [← canonical] at bodyRun
      have adjusted : Execution body ⟨some body.main,Function.update (data frame (count+1) source buffer)
          (some 14) (List.replicate count true)⟩
          ⟨none,data frame count suffix ((InstructionCodec.encode bound instruction).reverse++buffer)⟩ bodyTicks bodyPeak := by
        simpa only [data_decrement] using bodyRun
      obtain ⟨peak,trace⟩ := CountLoop.next (some 14) none Option.isNone counted adjusted (by simp [data_at]) tailRun
      have widthBound : width ≤ budget := (WordListTotal.stored_width_le_ambient frame width ready.stored).trans (by omega)
      have registerBound : registers ≤ budget := (InstructionRange.stored_registers_le_ambient frame registers ready.saved).trans (by omega)
      have current := valid_cost width registers budget widthBound registerBound
      refine ⟨_,bodyTicks+tailTicks+1,peak,trace,rfl,?_,?_⟩
      · simp only [InstructionCodec.readMany, decoded, Bind.bind, Option.bind]
        cases tailRead : InstructionCodec.readMany width registers count suffix <;> simpa only [tailRead, Option.bind_none,
          Option.bind_some, Option.isSome_none, Option.isSome_some, Option.pure_def] using tailStatus
      · simp only [Nat.add_mul, Nat.one_mul]
        omega
    | none =>
      obtain ⟨final,ticks,peak,reading,halted,status,timeBound,_⟩ := InstructionFrontend.total_resources (fields frame count buffer)
        width registers source (by simpa [fields] using ready.stored) (by simpa [fields] using ready.saved)
        (by simpa [fields] using ready.loopEmpty) (by simpa [fields] using ready.payloadEmpty) (by simpa [fields] using ready.countEmpty)
        (by simpa [fields] using ready.tagEmpty) (by simpa [fields] using ready.rangeEmpty) (by simpa [fields] using ready.scratchEmpty)
        (by simpa [fields] using ready.roleEmpty)
      have rejected : Option.isNone (final.stk none).head?=false := by simpa only [decoded, Option.isSome_none] using status
      have terminal : final=⟨none,final.stk⟩ := congrArg₂ State.mk halted rfl
      rw [terminal] at reading
      have stopped := GuardedLink.failure InstructionCollect.program none Option.isNone reading rejected
      have adjusted : Execution body ⟨some body.main,Function.update (data frame (count+1) source buffer)
          (some 14) (List.replicate count true)⟩ ⟨none,final.stk⟩ (ticks+1) peak := by
        rw [data_decrement]
        exact stopped
      obtain ⟨fullPeak,trace⟩ := CountLoop.reject (some 14) none Option.isNone counted adjusted rejected
      have sizeBound : source.length+ambientBits (fields frame count buffer) ≤ budget := by
        rw [ambient_fields frame count buffer countEmpty bufferEmpty]
        omega
      have current := frontend_cost _ budget sizeBound
      refine ⟨_,(ticks+1)+2,fullPeak,trace,rfl,?_,?_⟩
      · simpa only [InstructionCodec.readMany, decoded, Bind.bind, Option.bind, Option.isSome_none] using rejected
      · simp only [Nat.add_mul, Nat.one_mul]
        omega

theorem payload_total (frame : Port → List Bool) (bound : registers ≤ 2^width) (count : Nat)
    (source : List Bool) (budget : Nat) (ready : Workspace frame width registers)
    (countEmpty : frame (some 14)=[]) (bufferEmpty : frame (some 19)=[])
    (mass : count+source.length+ambientBits frame ≤ budget) :
    ∃ final ticks peak, Execution restorePayload ⟨some restorePayload.main,data frame count source []⟩ final ticks peak ∧
      final.pc=none ∧ Option.isNone (final.stk none).head?=(InstructionCodec.readMany width registers count source).isSome ∧
      ticks ≤ count*cost budget+6*source.length+8 := by
  obtain ⟨final,ticks,peak,loopRun,halted,status,timeBound⟩ := loop_total frame bound count source [] budget ready countEmpty bufferEmpty
    (by simpa only [List.length_nil, Nat.add_zero] using mass)
  cases decoded : InstructionCodec.readMany width registers count source with
  | none =>
    have rejected : Option.isNone (final.stk none).head?=false := by simpa only [decoded, Option.isSome_none] using status
    have terminal : final=⟨none,final.stk⟩ := congrArg₂ State.mk halted rfl
    rw [terminal] at loopRun
    have trace := GuardedLink.failure restoreMachine none Option.isNone loopRun rejected
    exact ⟨_,ticks+1,peak,trace,rfl,by simpa only [decoded, Option.isSome_none] using rejected,by omega⟩
  | some pair =>
    rcases pair with ⟨instructions,suffix⟩
    obtain ⟨length,canonical⟩ := ProgramSyntax.readMany_inverse bound count source instructions suffix decoded
    obtain ⟨otherTicks,otherPeak,otherRun,_⟩ := loop_execution frame bound instructions suffix [] ready.stored ready.saved
      ready.loopEmpty ready.payloadEmpty ready.countEmpty ready.tagEmpty ready.rangeEmpty ready.scratchEmpty ready.roleEmpty ready.temporaryEmpty
    simp only [List.append_nil] at otherRun
    rw [length, ← canonical] at otherRun
    have finalEq := InstructionFrontend.terminal_unique loopRun otherRun halted rfl
    rw [finalEq] at loopRun
    obtain ⟨restorePeak,restoring⟩ := restore_execution frame suffix (InstructionCodec.encodeMany bound instructions).reverse
    simp only [List.reverse_reverse, List.length_reverse] at restoring
    have trace := GuardedLink.success none Option.isNone loopRun restoring (by simp [data_at])
    have codeBound : (InstructionCodec.encodeMany bound instructions).length ≤ source.length := by
      have size := congrArg List.length canonical
      simp only [List.length_append] at size
      omega
    exact ⟨_,_,_,trace,rfl,by simp [data_at],by omega⟩

def polynomial (size : Nat) : Nat := 32*size^4+256*size^3+400*size^2+415*size+16

theorem whole_time (count payload size ticks : Nat)
    (countBound : count ≤ size) (payloadBound : payload ≤ size)
    (bound : ticks ≤ count*cost (2*size)+6*payload+8) :
    (4*count+4)+(5*count+4+ticks) ≤ polynomial size := by
  have overhead : (4*count+4)+(5*count+4+ticks) ≤ count*(cost (2*size)+9)+6*payload+16 := by
    have identity : count*(cost (2*size)+9)=count*cost (2*size)+9*count := by ring
    omega
  have product := Nat.mul_le_mul_right (cost (2*size)+9) countBound
  have growth := Nat.mul_le_mul_left 6 payloadBound
  have identity : size*(cost (2*size)+9)+6*size+16=polynomial size := by unfold cost polynomial; ring
  exact overhead.trans ((show count*(cost (2*size)+9)+6*payload+16 ≤ size*(cost (2*size)+9)+6*size+16 by omega).trans_eq identity)

abbrev program := ProgramReader.program

theorem total_resources (frame : Port → List Bool) (bound : registers ≤ 2^width) (input : List Bool)
    (ready : Workspace frame width registers) (countEmpty : frame (some 14)=[])
    (savedEmpty : frame (some 15)=[]) (bufferEmpty : frame (some 19)=[]) :
    let size := input.length+ambientBits frame
    ∃ final ticks peak, Execution program ⟨some program.main,bank frame [] input []⟩ final ticks peak ∧
      final.pc=none ∧ Option.isNone (final.stk none).head?=(ProgramSyntax.readPrefix width registers input).isSome ∧
      ticks ≤ polynomial size ∧ peak ≤ polynomial size+size := by
  let size := input.length+ambientBits frame
  cases parsed : Encoding.readCount input with
  | none =>
    have canonical := HeaderParser.readCount_none parsed
    have header := ColdInput.read_save_eof frame 14 input.length []
    rw [← canonical] at header
    have trace := GuardedLink.failure payloadProgram none Option.isNone header (by simp [bank_counter])
    have inputBound : input.length ≤ size := by dsimp [size]; omega
    have timeBound : 2*input.length+4+1 ≤ polynomial size := by unfold polynomial; omega
    have space := trace.peak_le
    simp only [bank_live, List.length_nil, Nat.zero_add, Nat.add_zero] at space
    change _ ≤ size+(2*input.length+4+1) at space
    have ordered : size+(2*input.length+4+1) ≤ polynomial size+size := by omega
    exact ⟨_,_,_,trace,rfl,by simp [bank_counter, ProgramSyntax.readPrefix, parsed],timeBound,space.trans ordered⟩
  | some pair =>
    rcases pair with ⟨count,payload⟩
    let savedFrame := Function.update frame (some 15) (List.replicate count true)
    have savedReady : Workspace savedFrame width registers := {
      stored := by simp [savedFrame, ready.stored]
      saved := by simp [savedFrame, ready.saved]
      loopEmpty := by simp [savedFrame, ready.loopEmpty]
      payloadEmpty := by simp [savedFrame, ready.payloadEmpty]
      countEmpty := by simp [savedFrame, ready.countEmpty]
      tagEmpty := by simp [savedFrame, ready.tagEmpty]
      rangeEmpty := by simp [savedFrame, ready.rangeEmpty]
      scratchEmpty := by simp [savedFrame, ready.scratchEmpty]
      roleEmpty := by simp [savedFrame, ready.roleEmpty]
      temporaryEmpty := by simp [savedFrame, ready.temporaryEmpty] }
    have canonical := HeaderParser.readCount_sound parsed
    have length : input.length=count+payload.length+1 := by rw [canonical]; simp [Encoding.frameCount]; omega
    have ambient : ambientBits savedFrame=ambientBits frame+count := by
      simpa only [savedFrame, List.length_replicate] using
        ColdInput.ambient_saved frame 15 (by decide) (by decide) (by decide) (List.replicate count true) savedEmpty
    have mass : count+payload.length+ambientBits savedFrame ≤ 2*size := by rw [ambient]; dsimp [size]; omega
    obtain ⟨final,ticks,peak,payloadRun,halted,status,payloadBound⟩ := payload_total savedFrame bound count payload (2*size) savedReady
      (by simp [savedFrame, countEmpty]) (by simp [savedFrame, bufferEmpty]) mass
    have terminal : final=⟨none,final.stk⟩ := congrArg₂ State.mk halted rfl
    rw [terminal] at payloadRun
    obtain ⟨copyPeak,copying⟩ := copy_count_execution frame count payload savedEmpty
    have tail := copying.link payloadRun
    have header := ColdInput.read_save_execution frame 14 (by decide) (by decide) (by decide) count payload [] countEmpty
    rw [header_data frame count payload bufferEmpty, ← canonical] at header
    have trace := GuardedLink.success none Option.isNone header tail (by simp [data_at])
    have countBound : count ≤ size := by dsimp [size]; omega
    have suffixBound : payload.length ≤ size := by dsimp [size]; omega
    have timeBound := whole_time count payload.length size ticks countBound suffixBound payloadBound
    have space := trace.peak_le
    simp only [bank_live, List.length_nil, Nat.zero_add, Nat.add_zero] at space
    change _ ≤ size+((4*count+4)+(5*count+4+ticks)) at space
    have ordered : size+((4*count+4)+(5*count+4+ticks)) ≤ polynomial size+size := by omega
    refine ⟨_,_,_,trace,rfl,?_,timeBound,space.trans ordered⟩
    simpa only [ProgramSyntax.readPrefix, parsed, Bind.bind, Option.bind] using status

theorem total_decodes (frame : Port → List Bool) (bound : registers ≤ 2^width) (input : List Bool)
    (ready : Workspace frame width registers) (countEmpty : frame (some 14)=[])
    (savedEmpty : frame (some 15)=[]) (bufferEmpty : frame (some 19)=[]) :
    let size := input.length+ambientBits frame
    ∃ final ticks peak, Execution program ⟨some program.main,bank frame [] input []⟩ final ticks peak ∧
      final.pc=none ∧ Option.isNone (final.stk none).head?=(ProgramSyntax.readPrefix width registers input).isSome ∧
      (∀ instructions suffix, ProgramSyntax.readPrefix width registers input=some (instructions,suffix) →
        final.stk=data (Function.update frame (some 15) (List.replicate instructions.length true)) 0 suffix
          (InstructionCodec.encodeMany bound instructions) ∧
        ProgramReader.observe width registers final.stk=some instructions.toArray ∧ final.stk (some 0)=suffix) ∧
      ticks ≤ polynomial size ∧ peak ≤ polynomial size+size := by
  obtain ⟨final,ticks,peak,trace,halted,status,timeBound,spaceBound⟩ := total_resources frame bound input ready countEmpty savedEmpty bufferEmpty
  refine ⟨final,ticks,peak,trace,halted,status,?_,timeBound,spaceBound⟩
  intro instructions suffix decoded
  have canonical := ProgramSyntax.prefix_inverse bound input instructions suffix decoded
  obtain ⟨otherTicks,otherPeak,other,_,_⟩ := ProgramReader.execution frame bound instructions suffix ready.stored ready.saved
    ready.loopEmpty ready.payloadEmpty ready.countEmpty ready.tagEmpty countEmpty savedEmpty ready.rangeEmpty ready.scratchEmpty ready.roleEmpty bufferEmpty ready.temporaryEmpty
  rw [← canonical] at other
  have same := InstructionFrontend.terminal_unique trace other halted rfl
  rw [same]
  exact ⟨rfl,ProgramReader.endpoint_observation frame bound instructions suffix,by simp [data_at]⟩

end Controller.Complexity.ProgramTotal
