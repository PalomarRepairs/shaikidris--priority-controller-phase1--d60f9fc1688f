module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.PcAdvance
public import Controller.Complexity.StateNative

@[expose] public section

/-! The simulation relation identifies every actual native state-field packet
and both global headers. It implies literal native State decoding and supports
physical workspace preservation and exact PC/halt state updates. -/
namespace Controller.Complexity.NativeStore
open WordReader

structure Stored (input : Port → List Bool) (state : Controller.Cost.State width registers) : Prop where
  widthStored : input (some 8)=List.replicate width true
  countStored : input (some 9)=List.replicate registers true
  registersStored : input (some 21)=Encoding.encodeWords width (List.ofFn state.reg)
  heapStored : input (some 22)=Encoding.encodeWords width state.heap.toList
  stackStored : input (some 23)=Encoding.encodeWords width state.stack
  outputStored : input (some 24)=Encoding.encodeWords width state.output
  pcStored : input (some 25)=Encoding.encodeWords width [state.pc]
  haltStored : input (some 26)=[state.halted]

theorem Stored.bytes (input : Port → List Bool) (state : Controller.Cost.State width registers) (stored : Stored input state) :
    StateNative.storedBytes input=MachineBridge.encodeState state := by
  simp only [StateNative.storedBytes,MachineBridge.encodeState,stored.registersStored,stored.heapStored,stored.stackStored,
    stored.outputStored,stored.pcStored,stored.haltStored]

theorem Stored.observation (input : Port → List Bool) (state : Controller.Cost.State width registers) (stored : Stored input state) :
    StateNative.observe width registers input=some state := by
  rw [StateNative.observe,stored.bytes input state]
  exact MachineBridge.decode_encode state

def statePorts : List Port := [some 8,some 9,some 21,some 22,some 23,some 24,some 25,some 26]

theorem Stored.update_other (input : Port → List Bool) (state : Controller.Cost.State width registers) (stored : Stored input state)
    (port : Port) (value : List Bool) (outside : port ∉ statePorts) : Stored (Function.update input port value) state := by
  have different (target : Port) (member : target ∈ statePorts) : target ≠ port := by intro equal; subst target; exact outside member
  constructor
  · simpa only [Function.update_of_ne (different (some 8) (by simp [statePorts]))] using stored.widthStored
  · simpa only [Function.update_of_ne (different (some 9) (by simp [statePorts]))] using stored.countStored
  · simpa only [Function.update_of_ne (different (some 21) (by simp [statePorts]))] using stored.registersStored
  · simpa only [Function.update_of_ne (different (some 22) (by simp [statePorts]))] using stored.heapStored
  · simpa only [Function.update_of_ne (different (some 23) (by simp [statePorts]))] using stored.stackStored
  · simpa only [Function.update_of_ne (different (some 24) (by simp [statePorts]))] using stored.outputStored
  · simpa only [Function.update_of_ne (different (some 25) (by simp [statePorts]))] using stored.pcStored
  · simpa only [Function.update_of_ne (different (some 26) (by simp [statePorts]))] using stored.haltStored

theorem Stored.advance (input : Port → List Bool) (state : Controller.Cost.State width registers) (stored : Stored input state) :
    Stored (PcAdvance.output input state.pc) state.advance := by
  constructor
  · simpa [PcAdvance.output,FieldGet.field,Controller.Cost.State.advance] using stored.widthStored
  · simpa [PcAdvance.output,FieldGet.field,Controller.Cost.State.advance] using stored.countStored
  · simpa [PcAdvance.output,FieldGet.field,Controller.Cost.State.advance] using stored.registersStored
  · simpa [PcAdvance.output,FieldGet.field,Controller.Cost.State.advance] using stored.heapStored
  · simpa [PcAdvance.output,FieldGet.field,Controller.Cost.State.advance] using stored.stackStored
  · simpa [PcAdvance.output,FieldGet.field,Controller.Cost.State.advance] using stored.outputStored
  · simp [PcAdvance.output,FieldGet.field,Controller.Cost.State.advance,PcAdvance.next]
  · simpa [PcAdvance.output,FieldGet.field,Controller.Cost.State.advance] using stored.haltStored

def haltedOutput (input : Port → List Bool) := Function.update input (some 26) [true]

theorem Stored.halted (input : Port → List Bool) (state : Controller.Cost.State width registers) (stored : Stored input state) :
    Stored (haltedOutput input) { state with halted := true } := by
  constructor
  · simpa [haltedOutput] using stored.widthStored
  · simpa [haltedOutput] using stored.countStored
  · simpa [haltedOutput] using stored.registersStored
  · simpa [haltedOutput] using stored.heapStored
  · simpa [haltedOutput] using stored.stackStored
  · simpa [haltedOutput] using stored.outputStored
  · simpa [haltedOutput] using stored.pcStored
  · simp [haltedOutput]

end Controller.Complexity.NativeStore
