import Mathlib

theorem algebra_2227 {a b : ℝ} (h : 19 * a + 98 * b = 0) : a * b ≤ 0 := by
  have ha : a = -98/19 * b := by
    linarith
  rw [ha]
  have h1 : (-98/19 * b) * b ≤ 0 := by
    have h2 : b ^ 2 ≥ 0 := sq_nonneg b
    nlinarith
  linarith