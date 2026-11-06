import Mathlib

theorem algebra_327019 (a b c : ℝ) (h1 : a + 2 * b + 3 * c = 6) (h2 : a ^ 2 + 4 * b ^ 2 + 9 * c ^ 2 = 12) :
    a * b * c = 4 / 3 := by

  have h3 : (a - 2) ^ 2 + 4 * (b - 1) ^ 2 + 9 * (c - 2/3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (2 * b - 3 * c), sq_nonneg (a - 2), sq_nonneg (b - 1), sq_nonneg (c - 2 / 3)]
  have h4 : a - 2 = 0 := by
    nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 1), sq_nonneg (c - 2 / 3)]
  have h5 : b - 1 = 0 := by
    nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 1), sq_nonneg (c - 2 / 3)]
  have h6 : c - 2 / 3 = 0 := by
    nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 1), sq_nonneg (c - 2 / 3)]
  have ha : a = 2 := by linarith
  have hb : b = 1 := by linarith
  have hc : c = 2 / 3 := by linarith
  rw [ha, hb, hc]
  norm_num