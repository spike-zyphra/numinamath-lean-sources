import Mathlib

open Real Set
open scoped Real

theorem algebra_163821 (α : ℝ) :
  (cos (2 * α))^2 - 3 * (sin (2 * α))^2 =
  4 * sin (π / 6 + 2 * α) * sin (π / 6 - 2 * α) := by

  have h1 : sin (π / 6) = 1 / 2 := by
    rw [sin_pi_div_six]
  have h2 : cos (π / 6) = Real.sqrt 3 / 2 := by
    rw [cos_pi_div_six]

  have h3 : sin (π / 6 + 2 * α) = sin (π / 6) * cos (2 * α) + cos (π / 6) * sin (2 * α) := by
    rw [sin_add]

  have h4 : sin (π / 6 - 2 * α) = sin (π / 6) * cos (2 * α) - cos (π / 6) * sin (2 * α) := by
    rw [sin_sub]

  rw [h3, h4, h1, h2]

  have h5 : 4 * ( ( (1 / 2 : ℝ) * cos (2 * α) + (Real.sqrt 3 / 2) * sin (2 * α) ) * ( ( (1 / 2 : ℝ) * cos (2 * α) - (Real.sqrt 3 / 2) * sin (2 * α) ) ) ) =
          (cos (2 * α))^2 - 3 * (sin (2 * α))^2 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

  linarith [h5]