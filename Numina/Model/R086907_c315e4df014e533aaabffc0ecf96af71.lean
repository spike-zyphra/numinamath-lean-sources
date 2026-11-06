import Mathlib

theorem algebra_199612 (d : ℝ) (h : d > 0) (a k : ℝ) (ha : 0 < a) (hk : 0 < k)
    (h1 : a = d * (1 - k / 2)) (h2 : d * (1 - k / 2) = a * (1 + k / 2)) :
    d = 2 * a * k := by
  rw [h1] at h2
  nlinarith [sq_nonneg (d), sq_nonneg (k - 2), mul_pos h ha, mul_pos ha hk]