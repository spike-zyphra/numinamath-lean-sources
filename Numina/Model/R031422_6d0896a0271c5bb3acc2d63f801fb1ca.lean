import Mathlib

open Real Set

theorem inequalities_554 (x : ℝ) :
    sin (x / 2) ^ 2 * cos (x / 2) ^ 6 ≤ 27 / 256 := by
  have h1 : sin (x / 2) ^ 2 + cos (x / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (x / 2)
  have h2 : sin (x / 2) ^ 2 = 1 - cos (x / 2) ^ 2 := by linarith
  have h3 : sin (x / 2) ^ 2 ≥ 0 := by positivity
  have h4 : cos (x / 2) ^ 2 ≥ 0 := by positivity
  nlinarith [sq_nonneg (sin (x / 2) ^ 2 - 1 / 4), sq_nonneg (sin (x / 2) ^ 2 - 1 / 4), 
    sq_nonneg (cos (x / 2) ^ 2 - 3 / 4), sq_nonneg (cos (x / 2) ^ 2 - 3 / 4), 
    sq_nonneg (sin (x / 2) ^ 2 * sin (x / 2) ^ 2 - 1 / 16), sq_nonneg ((cos (x / 2) ^ 2 - 3 / 4)^2), 
    sq_nonneg ((sin (x / 2) ^ 2 - 1 / 4) * (cos (x / 2) ^ 2 - 3 / 4)), 
    mul_nonneg (show 0 ≤ sin (x / 2) ^ 2 by positivity) (show 0 ≤ cos (x / 2) ^ 2 by positivity), 
    sq_nonneg (sin (x / 2) ^ 2 - cos (x / 2) ^ 2 + 1 / 2), 
    sq_nonneg (sin (x / 2) ^ 2 - cos (x / 2) ^ 2 - 1 / 2), 
    sq_nonneg (sin (x / 2) ^ 2 * cos (x / 2) ^ 2 * (cos (x / 2) ^ 2) * sin (x / 2) ^ 2 - 27 / 256 * sin (x / 2) ^ 2 * cos (x / 2) ^ 2)
  ]