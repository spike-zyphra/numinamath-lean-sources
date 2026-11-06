import Mathlib

theorem algebra_911 {a : ℝ} (ha : a ^ 3 + 2 * a = -2) :
  3 * a ^ 6 + 12 * a ^ 4 - a ^ 3 + 12 * a ^ 2 - 2 * a - 4 = 10 := by 
  have h1 : a ^ 3 = -2 - 2 * a := by linarith
  have h2 : a ^ 4 = a * a ^ 3 := by ring
  rw [h1] at h2
  have h3 : a ^ 4 = -2 * a - 2 * a ^ 2 := by
    nlinarith
  have h4 : a ^ 6 = (a ^ 3) ^ 2 := by ring
  rw [h1] at h4
  have h5 : a ^ 6 = 4 + 8 * a + 4 * a ^ 2 := by
    nlinarith [sq_nonneg (a + 1)]
  nlinarith [sq_nonneg (a ^ 2), sq_nonneg (a + 1), sq_nonneg (a - (-1))]