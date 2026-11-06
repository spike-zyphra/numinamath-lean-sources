import Mathlib

open Real 

theorem Algebra_608393 {t : ℝ} (h : (100 * t - (1/2) * t^2 = 1875 + (1/2) * t^2)): 
  t = 25 ∨ t = 75 := by
  have h1 : t^2 - 100 * t + 1875 = 0 := by
    nlinarith
  have h2 : (t - 25) * (t - 75) = 0 := by
    nlinarith [h1]
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case where t - 25 = 0, so t = 25
    left
    linarith
  · -- Case where t - 75 = 0, so t = 75
    right
    linarith