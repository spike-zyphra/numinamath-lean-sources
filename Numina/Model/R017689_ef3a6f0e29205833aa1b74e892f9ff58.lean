import Mathlib

theorem algebra_187964 {x : ℝ} (h1 : (2 * x ^ 2 + 3 * x - 1) ^ 2 - 5 * (2 * x ^ 2 + 3 * x + 3) + 24 = 0)
    (h2 : (x - 1) * (x + 3) * (x + 4) * (x + 8) = -96) (h3 : (x - 1) * (x - 2) * (x - 4) * (x - 8) = 4 * x ^ 2) :
    x = 1 ∨ x = -2 ∨ x = 1 / 2 ∨ x = -5 / 2 ∨ x = 0 ∨ x = -7 ∨ x = -1 / 2 * Real.sqrt 33 ∨ x = 5 * Real.sqrt 17 := by 
  nlinarith [sq_nonneg (x ^ 2 + x - 2), sq_nonneg (x ^ 2 - 2 * x + 1), sq_nonneg (x + 7), sq_nonneg (x * (x - 1)), sq_nonneg (x * (x + 1)), sq_nonneg ((2 * x + 5) * (2 * x - 1)), sq_nonneg ((x ^ 2 - 2 * x + 4) - (4 * x ^ 2)), sq_nonneg ((x ^ 2) - (x * 6 + 8)), Real.sqrt_pos.mpr (show (0 : ℝ) < (17 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num), sq_nonneg ((x - 1/2)), sq_nonneg ((x + 7))]