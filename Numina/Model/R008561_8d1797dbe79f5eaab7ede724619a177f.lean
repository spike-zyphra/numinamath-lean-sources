import Mathlib

theorem algebra_15724 {x : ℝ} (hx : x > 0) (h : x * 10000 = 4 / x) : x = 0.02 := by
  have h1 : x * 10000 * x = 4 := by
    have h2 : x ≠ 0 := by linarith
    field_simp [h2] at h ⊢
    nlinarith
  have h4 : x ^ 2 = (1 : ℝ) / 2500 := by
    nlinarith
  have h5 : x = (1 / 50 : ℝ) := by
    nlinarith [sq_nonneg (x - 1 / 50), h4, hx]
  rw [h5]
  norm_num