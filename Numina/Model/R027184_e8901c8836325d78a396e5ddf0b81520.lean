import Mathlib

theorem algebra_4557 {a b : ℝ} (ha : a ≠ 0) (h : a * (Real.sqrt 7 + 1)^2 - 8 * (Real.sqrt 7 + 1) + 6 = 0)
    (h1 : a = (5 * Real.sqrt 7 + b) / 3) : b = -8 := by
  have h2 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have eq3 : a * (Real.sqrt 7 + 1) ^ 2 - 8 * (Real.sqrt 7 + 1) + 6 =
      8 * a + 2 * a * Real.sqrt 7 - 8 * Real.sqrt 7 - 2 := by
    nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)]
  rw [eq3] at h 
  rw [show a = (5 * Real.sqrt 7 + b) / 3 by linarith [h1]] at h
  nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), sq_nonneg (Real.sqrt 7), sq_nonneg (b), sq_nonneg (a), sq_nonneg (Real.sqrt 7 - 2), sq_nonneg (b + 8)]