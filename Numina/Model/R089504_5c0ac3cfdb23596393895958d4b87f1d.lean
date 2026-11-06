import Mathlib

theorem algebra_598536 (a b c d e : ℝ) (h1 : a + b + c + d + e = 8) (h2 : a^2 + b^2 + c^2 + d^2 + e^2 = 16) :
    0 ≤ e ∧ e ≤ 16 / 5 := by
  have h3 : a + b + c + d = 8 - e := by linarith
  have h4 : a^2 + b^2 + c^2 + d^2 = 16 - e^2 := by linarith
  have h5 : a^2 + b^2 + c^2 + d^2 ≥ ((a + b + c + d)^2) / 4 := by
    linarith [sq_nonneg (a + b + c + d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
  rw [h3] at h5
  rw [h4] at h5
  have h6 : 16 * e - 5 * e^2 ≥ 0 := by
    nlinarith
  constructor
  · -- Show that 0 ≤ e
    nlinarith
  · -- Show that e ≤ 16/5
    nlinarith