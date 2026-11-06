import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_188873 {V1 V2 : ℝ}
  (hV1 : V1 = ∫ x in (-4)..4, π * (4^2 - x^2) / 8)
  (hV2 : V2 = ∫ x in (-4)..4, π * (4^2 - x^2) / 8) :
  V1 = V2 := by 
  rw [hV1, hV2]