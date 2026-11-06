import Mathlib
open Real Set

theorem calculus_9959 {V1 V2 : ℝ}
    (hV1 : V1 = ∫ x in (-4)..4, π * (-x^2 - 4) ^ 2)
    (hV2 : V2 = ∫ x in (-4)..4, π * (x^2 + 4) ^ 2) :
    V1 = V2 := by
  rw [hV1, hV2]
  congr
  funext x
  have h1 : (-x^2 - 4 : ℝ) ^ 2 = (x^2 + 4 : ℝ) ^ 2 := by
    ring_nf
  simp [h1]
  all_goals linarith