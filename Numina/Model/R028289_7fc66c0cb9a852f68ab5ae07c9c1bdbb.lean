import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_321484 (x y : ℝ) (h : x^2 + y^2 = 1) :
  |x^2 + 2 * x * y - y^2| ≤ sqrt 2 := by
  have h1 : (x ^ 2 + 2 * x * y - y ^ 2) ^ 2 ≤ 2 := by
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2 - 2 * x * y), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (2 * x * y)]
  have h2 : |x^2 + 2 * x * y - y^2| ≤ Real.sqrt 2 := by
    have h3 : (x^2 + 2 * x * y - y^2) ^ 2 ≤ (2 : ℝ) := h1
    have h4 : |x^2 + 2 * x * y - y^2| = Real.sqrt ((x^2 + 2 * x * y - y^2) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h4]
    have h5 : Real.sqrt ((x^2 + 2 * x * y - y^2) ^ 2) ≤ Real.sqrt (2 : ℝ) := by
      apply Real.sqrt_le_sqrt
      linarith
    linarith
  simpa using h2