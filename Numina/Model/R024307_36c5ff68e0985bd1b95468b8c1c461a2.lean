import Mathlib

theorem inequalities_48122 (x y : ℝ) (h₀ : x * y = 1) :
    x ^ 2 + y ^ 2 ≥ 2 * Real.sqrt 2 * (x - y) := by
  have h2 : x ^ 2 + y ^ 2 = (x - y) ^ 2 + 2 := by
    have h3 : x * y = 1 := h₀
    nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), h3]
  have h1 : (x - y) ^ 2 + 2 ≥ 2 * Real.sqrt 2 * (x - y) := by
    nlinarith [sq_nonneg (x - y - Real.sqrt 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (x + y), sq_nonneg (x - y), h₀]
  linarith [h2, h1]