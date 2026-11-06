import Mathlib

open Real

theorem algebra_59172 {x : ℝ} (hx : x = sin (π / 18)) :
    8 * x ^ 3 - 6 * x + 1 = 0 := by 
  have h1 : x = sin (π / 18) := hx
  have h2 : sin (π / 6) = 1 / 2 := by 
    rw [sin_pi_div_six]
  have h3 : sin (π / 6) = 3 * sin (π / 18) - 4 * sin (π / 18) ^ 3 := by
    have h1 : 3 * (π / 18) = π / 6 := by 
      ring
    rw [←h1]
    rw [sin_three_mul]
  have eq1 : 4 * sin (π / 18) ^ 3 - 3 * sin (π / 18) + 1 / 2 = 0 := by
    nlinarith [h3, h2]
  have eq2 : 8 * sin (π / 18) ^ 3 - 6 * sin (π / 18) + 1 = 0 := by
    nlinarith [eq1]
  rw [h1]
  nlinarith [eq2]