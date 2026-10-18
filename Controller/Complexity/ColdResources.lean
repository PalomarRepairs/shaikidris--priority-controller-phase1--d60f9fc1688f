module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.NativeLoop

@[expose] public section

/-! Scalar bounds for cold parsing, native interpretation and physical
return. Operational proofs instantiate these lemmas with actual traces;
their arithmetic does not expand the underlying encoded state expressions. -/
namespace Controller.Complexity.ColdResources

theorem space_mono {first second : Nat} (envelope : Nat) (bound : first ≤ second) :
    NativeLoop.space first envelope ≤ NativeLoop.space second envelope := by
  unfold NativeLoop.space
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (max_le_max bound (Nat.le_refl _))) 45

theorem accepted (size parserBound envelope nativeTicks parseTicks parsePeak parsedMass runTicks runPeak runMass returnTicks returnPeak : Nat)
    (parseTime : parseTicks ≤ parserBound) (parseSpace : parsePeak ≤ parserBound+size)
    (parsedSize : parsedMass ≤ parserBound+size)
    (runTime : runTicks ≤ parsedMass+nativeTicks*NativeLoop.perStep envelope+5*NativeLoop.space parsedMass envelope+30)
    (runSpace : runPeak ≤ 6*NativeLoop.space parsedMass envelope+28)
    (runSize : runMass ≤ 6*NativeLoop.space parsedMass envelope+28)
    (returnTime : returnTicks ≤ runMass+63) (returnSpace : returnPeak ≤ 2*runMass+63) :
    parseTicks+runTicks+returnTicks ≤ size+2*parserBound+nativeTicks*NativeLoop.perStep envelope+
      11*NativeLoop.space (size+parserBound) envelope+121 ∧
    max (max parsePeak runPeak) returnPeak ≤ 12*NativeLoop.space (size+parserBound) envelope+119 := by
  have mono := space_mono envelope (show parsedMass ≤ size+parserBound by omega)
  have initial : size+parserBound ≤ NativeLoop.space (size+parserBound) envelope := by
    have lower := le_max_left (size+parserBound) (envelope+NativeStep.budget envelope)
    unfold NativeLoop.space
    omega
  constructor <;> omega

theorem rejected (size parserBound parseTicks parsePeak parsedMass statusLength rejectPeak rejectMass returnTicks returnPeak : Nat)
    (parseTime : parseTicks ≤ parserBound) (parseSpace : parsePeak ≤ parserBound+size)
    (parsedSize : parsedMass ≤ parserBound+size) (statusSize : statusLength ≤ parsedMass)
    (rejectSpace : rejectPeak ≤ parsedMass+(statusLength+4)) (rejectSize : rejectMass ≤ parsedMass+1)
    (returnTime : returnTicks ≤ rejectMass+63) (returnSpace : returnPeak ≤ 2*rejectMass+63) :
    parseTicks+(statusLength+4)+returnTicks ≤ 3*parserBound+2*size+68 ∧
    max (max parsePeak rejectPeak) returnPeak ≤ 2*(parserBound+size)+65 := by constructor <;> omega

end Controller.Complexity.ColdResources
