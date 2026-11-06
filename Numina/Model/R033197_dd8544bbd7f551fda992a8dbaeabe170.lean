import Mathlib

open Real

theorem inequalities_104495 (x y : ℝ) (h : x^2 + y^2 ≠ 0) :
    (x + y) / (x^2 - x * y + y^2) ≤ 2 * sqrt 2 / sqrt (x^2 + y^2) := by
  have h1 : x^2 - x * y + y^2 > 0 := by
    nlinarith [sq_nonneg (x * y), sq_nonneg (x - y), sq_nonneg (x + y), sq_pos_of_ne_zero (show x ^ 2 + y ^ 2 ≠ 0 by assumption), sq_nonneg (x * x - y * y)]
  have h2 : sqrt (x^2 + y^2) > 0 := by
    apply sqrt_pos.2
    nlinarith [sq_pos_of_ne_zero (show x ^ 2 + y ^ 2 ≠ 0 by assumption)]
  have h3 : (x + y) * sqrt (x^2 + y^2) ≤ 2 * sqrt 2 * (x^2 - x * y + y^2) := by
    have h4 : 0 < sqrt (x^2 + y^2) := h2
    have h5 : 0 < x^2 - x * y + y^2 := h1
    nlinarith [sq_nonneg (x + y - y - x), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg ((x + y) - sqrt (x^2 + y^2) * sqrt 2), sq_nonneg ((x - y) * sqrt 2), sq_nonneg ((x + y) * sqrt 2 - sqrt (x^2 + y^2) * 2), sq_nonneg ((x^2 + y^2 - (x + y)^2 / 2) * sqrt 2), sq_nonneg ((x + y) / sqrt (x^2 + y^2) - sqrt 2 * ((x^2 - x * y + y^2) / (x^2 + y^2))), sq_nonneg (x * y - (x + y)^2 / 4), Real.sqrt_nonneg (x^2 + y^2), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (x^2 + y^2 : ℝ) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sqrt (x^2 + y^2) * sqrt 2 - (x + y)), sq_nonneg (sqrt (x^2 + y^2) - (x + y) / sqrt 2), sq_nonneg ((x + y) * sqrt 2 - sqrt (x^2 + y^2) * 2), sq_nonneg (x^2 + y^2 - (x + y) ^ 2 / 2), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (x + y - (x^2 - x * y + y^2) * (2 * sqrt 2) / sqrt (x^2 + y^2)), sq_nonneg ((x^2 - x * y + y^2) * (2 * sqrt 2) / sqrt (x^2 + y^2) - (x + y)), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_nonneg (2 : ℝ), sq_nonneg (sqrt (x^2 + y^2) * sqrt 2 - (x + y) * sqrt 2), sq_nonneg ((x^2 - x * y + y^2) * sqrt 2 * 2 - (x + y) ^ 2 * sqrt 2), sq_nonneg ((x + y) * sqrt (x^2 + y^2) - 2 * sqrt 2 * (x^2 - x * y + y^2)), Real.sqrt_nonneg (x^2 + y^2), Real.sqrt_nonneg (2)]
  apply (div_le_div_iff (by positivity) (by positivity)).mpr
  nlinarith