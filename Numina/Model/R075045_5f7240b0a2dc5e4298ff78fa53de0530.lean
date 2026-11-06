import Mathlib

open Real

theorem algebra_319930 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a + b + c = 10) (h2 : a^2 + b^2 = c^2) :
    a * b ≤ 50 * (3 - 2 * sqrt 2) := by
  have h3 : c = 10 - a - b := by linarith
  rw [h3] at h2
  have h4 : a * b = 10 * (a + b) - 50 := by
    nlinarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - (10 - (10 - a - b))), sq_nonneg ( (10 - a - b) - (10 - a - b)), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (a - b), sq_nonneg (a + b - 5), sq_nonneg ( (10 - a - b) - 5), sq_nonneg (a - (5 - 2 * Real.sqrt 2 * 8)), sq_nonneg (b - (5 - 2 * Real.sqrt 2 * 8))]