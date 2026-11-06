import Mathlib

open Real Set

theorem algebra_192546 (a x y : ℝ) (h₀ : x + y = 2 * a - 1) (h₁ : x ^ 2 + y ^ 2 = a ^ 2 + 2 * a - 3) :
    x * y ≥ (11 - 6 * sqrt 2) / 4 := by
  have h2 : (x + y) ^ 2 = x^2 + y^2 + 2 * (x * y) := by
    ring
  rw [h₀, h₁] at h2
  have h3 : 2 * (x * y) = 3 * a^2 - 6 * a + 4 := by
    nlinarith
  have h4 : x * y = (3 * a^2 - 6 * a + 4) / 2 := by
    linarith
  have h5 : (2 * a - 1) ^ 2 - 4 * ((3 * a^2 - 6 * a + 4) / 2) ≥ 0 := by
    nlinarith [sq_nonneg (x - y)]
  have h6 : 2 * a^2 - 8 * a + 7 ≤ 0 := by
    nlinarith [h5]
  nlinarith [sq_nonneg (a - (2 - Real.sqrt 2 / 2)), sq_nonneg (a - (2 + Real.sqrt 2 / 2)), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_nonneg 2,
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]