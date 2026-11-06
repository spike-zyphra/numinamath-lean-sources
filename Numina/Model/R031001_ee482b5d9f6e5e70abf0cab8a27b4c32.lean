import Mathlib

open Real

theorem algebra_21097 {f : ℝ → ℝ} (hf : f = fun x => -2/sqrt 3 * x^2 + 7/(2*sqrt 3)) :
    dist (-sqrt 7/2) (sqrt 7/2) = sqrt 7 := by
  rw [dist_eq_norm]
  have h1 : (-sqrt 7 / 2 : ℝ) - (sqrt 7 / 2 : ℝ) = -sqrt 7 := by
    ring_nf
  rw [h1]
  rw [norm_neg]
  rw [norm_of_nonneg (show 0 ≤ sqrt 7 by positivity)]