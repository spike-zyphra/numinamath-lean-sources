import Mathlib

open Real Set
open scoped Real

theorem algebra_163160 (α : Real) :
  sin (6 * α) - 2 * sqrt 3 * (cos (3 * α))^2 + sqrt 3 =
  2 * sin (6 * α - π / 3) := by
    have h1 : cos (3 * α) ^ 2 = (1 + cos (6 * α)) / 2 := by
      have h1 : cos (6 * α) = 2 * cos (3 * α) ^ 2 - 1 := by
        rw [show 6 * α = 2 * (3 * α) by ring]
        rw [cos_two_mul]
      linarith
    rw [h1]
    have h2 : sin (6 * α) - 2 * sqrt 3 * ((1 + cos (6 * α)) / 2) + sqrt 3 =
      sin (6 * α) - sqrt 3 * cos (6 * α) := by
      ring
    rw [h2]
    have h3 : sin (6 * α) - sqrt 3 * cos (6 * α) = 2 * sin (6 * α - π / 3) := by
      rw [sin_sub]
      have h4 : cos (π / 3) = 1 / 2 := by
        rw [cos_pi_div_three]
      have h5 : sin (π / 3) = sqrt 3 / 2 := by
        rw [sin_pi_div_three]
      rw [h4, h5]
      ring
    linarith [h3]